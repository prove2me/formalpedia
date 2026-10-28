-- Prove2me | solution 2 for AvramDividend.Classical.separated_strict_passage_infima_no_finite_tie
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:26:36.213328+00:00
-- url     : https://prove2.me/submissions/35d71d59-2646-47b3-9404-9757e7677d21

import Mathlib.Topology.Order.LeftRightNhds
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_rightcontinuous_separated_strict_passages_no_finite_tie

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (lower upper : ℝ)
    (hsep : lower < upper)
    (hRight : ContinuousWithinAt f (Set.Ici t) t)
    (hUp : (t : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : upper < f s), (s : ℝ≥0∞)))
    (hDown : (t : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : f s < lower), (s : ℝ≥0∞))) :
    False := by 
  have hU := chat03_finite_extended_infimum_isGLB (fun s => upper < f s) (t : ℝ≥0∞) hUp
    ENNReal.coe_ne_top
  have hD := chat03_finite_extended_infimum_isGLB (fun s => f s < lower) (t : ℝ≥0∞) hDown
    ENNReal.coe_ne_top
  rw [ENNReal.toNNReal_coe] at hU hD
  exact chat03_rightcontinuous_separated_strict_passages_no_finite_tie f t lower upper hsep hRight hU hD
