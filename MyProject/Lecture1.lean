
import Mathlib.Tactic

/-
These are the formalisations of some (hopefully eventually all) of the exercises
in Ataiya-Macdonalds's Introduction to Commutative Algebra
-/

namespace Chapter1Exercises

variable (R : Type) [CommRing R]

open Ideal

example (x : R) : x ∈ jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit (x * y + 1) := by
  /-
  The math proof:
  (→) suppose x that 1-xy is not a unit, use zorn's lemma to find a maximal 𝓶 ⊇ (1-xy)
  as x ∈ 𝓙(R) it is in 𝓶 → xy ∈ 𝓶 → 1 ∈ 𝓶 → 𝓶 = R, a contradiction.
  (←) suppose 1-xy a unit but x ∉ 𝓶 maximal → (x)+𝓶 = R → xy+m=1 ∈ R for some y ∈ R and m ∈ 𝓶
  this gives m = 1-xy a unit, whihc contradicts m ∈ 𝓶.
  -/
  exact mem_jacobson_bot

open scoped BigOperators

open Finset

example (x : R) : 1 - x = 1 + (-x) := by exact sub_eq_add_neg 1 x

lemma sum_cancel (x : R) : (1 - x) * ∑ i in range n, x ^ i = 1 - x^n := by
  induction' n with d hd
  · simp
  · rw [Finset.sum_range_succ, left_distrib, hd, pow_succ]
    ring

theorem exercise_1_1 (x : R) (h : x ∈ nilradical R): IsUnit (1 - x) := by
  /-
  having 1 + x a unit is the original question, but this is equivalent and easier
  -/
  rw [mem_nilradical, isUnit_iff_exists_inv] at *
  obtain ⟨n, h⟩ := h
  use (∑ i in range n, x^i)
  rw [sum_cancel]
  simp [h]

open Polynomial

variable (f : R[X])

theorem exercise_1_2_i : IsUnit f ↔ IsUnit (coeff f 0) ∧ ∀ n > 0, IsNilpotent (coeff f n)  := by
  sorry

theorem exercise_1_2_ii : IsNilpotent f ↔ ∀ n ≥ 0, IsNilpotent (coeff f n) := by
  sorry

theorem exercise_1_2_iii : ∃ g, f * g = 0 ↔ ∃ (a : R), C a * f = 0 := by
  sorry

/-
Need to introduce a notion for primitive polynomials...
-/

theorem exercise_1_2_iv : IsUnit f ↔ IsUnit (coeff f 0) ∧ (∀ n > 0, IsNilpotent (coeff f n) ) := by
  sorry



theorem exercise_1_4 : jacobson (⊥ : Ideal R[X]) = nilradical R[X] := by
  sorry

theorem exercise_1_6 (I : Ideal R) (h : ∀ J : Ideal R, J ≤ nilradical R → ∃ e : R, e ∈ J ∧ e^2 = e) : jacobson (⊥ : Ideal R) = nilradical R := by
  ext x
  constructor
  · intro hxJ
    rw [mem_jacobson_bot] at hxJ
    specialize hxJ 1
    rw [isUnit_iff_exists] at hxJ
    rcases hxJ with ⟨y, ⟨_, hxy⟩⟩

example : jacobson (⊤ : Ideal R) = nilradical R := by
  sorry


  · rw []
    have h : ⊤ ≤ ⊥ := by
    exact jacobson_mono h --should be an exact of some sort
