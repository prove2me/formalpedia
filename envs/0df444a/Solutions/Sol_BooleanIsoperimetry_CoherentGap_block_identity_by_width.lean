-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.block_identity_by_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:43.934803+00:00
-- url     : https://prove2.me/submissions/5ce4a99f-a1cd-4da0-8bd6-6ccf8265219f

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_at_triangular_end
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_eq_iff
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyDifference_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_eq_block_start
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_next_block_start
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_correction_sum_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyHeight_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution :
    ∀ previous dimension : ℕ,
      guide dimension = previous + 1 →
        residual (previous + 1) dimension +
          ∑ index : Fin previous,
            conwayGuyHeight (triangular index.val) = 1
  | 0, dimension, hguide => by
      have hdimension : dimension = 2 := by
        obtain ⟨hlower, hupper⟩ :=
          (guide_eq_iff (dimension := dimension) (width := 1) (by omega)).mp
            hguide
        simp [triangular] at hlower hupper
        omega
      subst dimension
      have hguideTwo : guide 2 = 1 := by
        simpa [triangular] using guide_at_triangular_end 1
      have hheightOne : conwayGuyHeight 1 = 1 := by
        simp [conwayGuyHeight, conwayGuyDifference, difference]
      have hdifferenceOne : conwayGuyDifference 1 = 1 := by
        rw [conwayGuyDifference_succ, hguideTwo]
        simp [conwayGuyDifference, difference]
      have hheightTwo : conwayGuyHeight 2 = 2 := by
        rw [show 2 = 1 + 1 by omega, conwayGuyHeight_succ,
          hheightOne, hdifferenceOne]
        norm_num
      simp [residual, hheightOne, hheightTwo]
  | previous + 1, dimension, hguide => by
      have hstart :=
        residual_eq_block_start (width := previous + 2)
          (dimension := dimension) (by omega) hguide
      have hpreviousGuide :
          guide (triangular (previous + 1) + 1) = previous + 1 :=
        guide_at_triangular_end (previous + 1)
      have inductionHypothesis :=
        solution previous
          (triangular (previous + 1) + 1) hpreviousGuide
      have hpred :
          previous + 2 - 1 = previous + 1 := by omega
      rw [hpred] at hstart
      rw [hstart, residual_next_block_start, correction_sum_succ]
      linarith
end BooleanIsoperimetry.CoherentGap
