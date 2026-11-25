-- Prove2me | solution 1 for BeckFialaMatrix.slack_row_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:00:40.384122+00:00
-- url     : https://prove2.me/submissions/66273b8d-1928-4346-857b-588b4914f78c

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_BeckFialaMatrix_Basic
public import Theorems.Thm_BeckFialaMatrix_mem_floatingCoordinates

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1) (x : Fin N → ℚ)
    (y : Fin N → ℤ) (hy01 : ∀ i, y i = 0 ∨ y i = 1)
    (hagree : ∀ i ∉ floatingCoordinates x, (y i : ℚ) = x i) (j : Fin m)
    (hj : floatingDegree A x j ≤ t) :
    |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  classical
  have htQ : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
  set S := (floatingCoordinates x).filter (fun i => A j i = 1) with hS
  have hScard : (S.card : ℚ) ≤ (t : ℚ) := by
    have : S.card ≤ t := hj
    exact_mod_cast this
  have hsum : ∑ i, (A j i : ℚ) * ((y i : ℚ) - x i) = ∑ i ∈ S, ((y i : ℚ) - x i) := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have h1 : A j i = 1 := (Finset.mem_filter.mp hi).2
      rw [h1]; push_cast; ring
    · intro i _ hi
      simp only [hS, Finset.mem_filter, not_and] at hi
      by_cases hfl : i ∈ floatingCoordinates x
      · have h0 : A j i = 0 := (hA j i).resolve_right (hi hfl)
        rw [h0]; simp
      · rw [hagree i hfl]; ring
  rw [hsum]
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    simpa using lt_of_lt_of_le zero_lt_one htQ
  · have hterm : ∀ i ∈ S, |(y i : ℚ) - x i| < 1 := by
      intro i hi
      have hfl : i ∈ floatingCoordinates x := (Finset.mem_filter.mp hi).1
      rw [mem_floatingCoordinates] at hfl
      rcases hy01 i with h | h <;> rw [h] <;> push_cast <;> rw [abs_lt] <;>
        constructor <;> linarith [hfl.1, hfl.2]
    calc |∑ i ∈ S, ((y i : ℚ) - x i)| ≤ ∑ i ∈ S, |(y i : ℚ) - x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i ∈ S, (1 : ℚ) := Finset.sum_lt_sum_of_nonempty hne hterm
      _ = (S.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (t : ℚ) := hScard
end BeckFialaMatrix
