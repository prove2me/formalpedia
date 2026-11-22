-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.residual_next_block_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:23.299875+00:00
-- url     : https://prove2.me/submissions/f3e7a2eb-8c8f-42ad-8739-762c2ecab084

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_eq_iff
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyDifference_eq_height_window
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_succ_width
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (previous : ℕ) :
    residual (previous + 2) (triangular (previous + 1) + 2) =
      residual (previous + 1) (triangular (previous + 1) + 1) -
        conwayGuyHeight (triangular previous) := by
  have htriangular :
      triangular (previous + 1) = triangular previous + previous + 1 := by
    rfl
  have hnextGuide :
      guide (triangular (previous + 1) + 2) = previous + 2 := by
    apply (guide_eq_iff (by omega)).mpr
    constructor
    · have hpred :
          previous + 2 - 1 = previous + 1 := by omega
      rw [hpred]
    · have hnextTriangular :
          triangular (previous + 2) =
            triangular (previous + 1) + previous + 2 := by
          change triangular ((previous + 1) + 1) =
            triangular (previous + 1) + previous + 2
          rw [triangular]
          omega
      rw [hnextTriangular]
      omega
  have hwindow :=
    conwayGuyDifference_eq_height_window
      (triangular (previous + 1) + 1) (by omega)
  rw [hnextGuide] at hwindow
  have htail :
      triangular (previous + 1) + 1 - (previous + 2) =
        triangular previous := by
    omega
  rw [htail] at hwindow
  calc
    residual (previous + 2) (triangular (previous + 1) + 2) =
        residual (previous + 1) (triangular (previous + 1) + 1) +
          conwayGuyDifference (triangular (previous + 1) + 1) -
            conwayGuyHeight (triangular (previous + 1) + 1) := by
      simpa [Nat.add_assoc] using
        residual_succ_width (previous + 1)
          (triangular (previous + 1) + 1)
    _ = residual (previous + 1) (triangular (previous + 1) + 1) -
          conwayGuyHeight (triangular previous) := by
      rw [hwindow]
      ring
end BooleanIsoperimetry.CoherentGap
