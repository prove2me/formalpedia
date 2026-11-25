-- Prove2me | solution 1 for BeckFialaMatrix.exists_rounding_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:01.412558+00:00
-- url     : https://prove2.me/submissions/445cfd64-8cf8-4194-8359-ac3f6082918d

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
public import Theorems.Thm_BeckFialaMatrix_tight_card_lt
public import Theorems.Thm_BeckFialaMatrix_exists_null_vector
public import Theorems.Thm_BeckFialaMatrix_exists_step_along

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (j0 : Fin m) (hj0 : t < floatingDegree A x j0) :
    ∃ x' : Fin N → ℚ, (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) ∧
      (∀ i ∉ floatingCoordinates x, x' i = x i) ∧
      (floatingCoordinates x').card < (floatingCoordinates x).card ∧
      (∀ j, t < floatingDegree A x j → ∑ i, (A j i : ℚ) * x' i = ∑ i, (A j i : ℚ) * x i) := by
  classical
  set F := floatingCoordinates x with hFdef
  set T := univ.filter (fun j => t < floatingDegree A x j) with hTdef
  have hj0T : j0 ∈ T := by simp [hTdef, hj0]
  have hFne : F.Nonempty := by
    have : 0 < ((floatingCoordinates x).filter (fun i => A j0 i = 1)).card := by
      have := hj0; simp only [floatingDegree] at this; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, (Finset.mem_filter.mp hi).1⟩
  have hcard : T.card < F.card := tight_card_lt A hdeg x hFne
  obtain ⟨v, hv0, ⟨i0, hi0F, hvi0⟩, hvnull⟩ := exists_null_vector A F T hcard
  have hFmem : ∀ i ∈ F, 0 < x i ∧ x i < 1 := fun i hi => mem_floatingCoordinates.mp hi
  obtain ⟨s, hs, hrange, i1, hi1F, hi1⟩ :=
    exists_step_along x hx F hFmem v hv0 i0 hi0F hvi0
  refine ⟨fun i => x i + s * v i, hrange, ?_, ?_, ?_⟩
  · intro i hi
    simp only [hv0 i hi, mul_zero, add_zero]
  · have hsub : floatingCoordinates (fun i => x i + s * v i) ⊆ F := by
      intro i hi
      by_contra hiF
      rw [mem_floatingCoordinates] at hi
      simp only [hv0 i hiF, mul_zero, add_zero] at hi
      exact hiF (mem_floatingCoordinates.mpr hi)
    have hi1not : i1 ∉ floatingCoordinates (fun i => x i + s * v i) := by
      rw [mem_floatingCoordinates]
      rcases hi1 with h | h <;> simp [h]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨i1, hi1F, hi1not⟩)
  · intro j hj
    have hjT : j ∈ T := by simp [hTdef, hj]
    have := hvnull j hjT
    calc ∑ i, (A j i : ℚ) * (x i + s * v i)
        = (∑ i, (A j i : ℚ) * x i) + s * ∑ i, (A j i : ℚ) * v i := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i, (A j i : ℚ) * x i := by rw [this]; ring
end BeckFialaMatrix
