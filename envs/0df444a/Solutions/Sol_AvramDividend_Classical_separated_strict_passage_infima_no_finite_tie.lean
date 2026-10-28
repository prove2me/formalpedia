-- Prove2me | solution 1 for AvramDividend.Classical.separated_strict_passage_infima_no_finite_tie
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:26:12.681223+00:00
-- url     : https://prove2.me/submissions/9e25aed6-2b44-4a2e-825d-ac6922709f77

import Mathlib.Topology.Order.LeftRightNhds
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_rightcontinuous_separated_strict_passages_no_finite_tie

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (lower upper : ℝ)
    (hsep : lower < upper)
    (hRight : ContinuousWithinAt f (Set.Ici t) t)
    (hUp : (t : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : upper < f s), (s : ℝ≥0∞)))
    (hDown : (t : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : f s < lower), (s : ℝ≥0∞))) :
    False := by
  have hUpGLB : IsGLB {s : ℝ≥0 | upper < f s} t := by
    have h := chat03_finite_extended_infimum_isGLB
      (fun s : ℝ≥0 => upper < f s) (t : ℝ≥0∞) hUp (by simp)
    simpa using h
  have hDownGLB : IsGLB {s : ℝ≥0 | f s < lower} t := by
    have h := chat03_finite_extended_infimum_isGLB
      (fun s : ℝ≥0 => f s < lower) (t : ℝ≥0∞) hDown (by simp)
    simpa using h
  exact chat03_rightcontinuous_separated_strict_passages_no_finite_tie
    f t lower upper hsep hRight hUpGLB hDownGLB
