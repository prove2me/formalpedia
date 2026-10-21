-- Prove2me | solution 1 for AvramDividend.Classical.chat03_official_strict_passage_no_finite_ties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:16:44.678602+00:00
-- url     : https://prove2.me/submissions/585a918e-9595-4b9d-bca0-88881adf2acd

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_rightcontinuous_separated_strict_passages_no_finite_tie
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Exact official named strict passage times for separated barriers
cannot coincide at a finite deterministic time.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (t : ℝ≥0)
    (hup : twoSidedExitUpTime X upper ω = (t : ℝ≥0∞))
    (hdown : twoSidedExitDownTime X lower ω = (t : ℝ≥0∞)) :
    False := by
  have hGIUp :
      IsGLB {s : ℝ≥0 | upper < X.X s ω} t := by
    have h :=
      chat03_finite_extended_infimum_isGLB
        (fun s : ℝ≥0 => upper < X.X s ω)
        (twoSidedExitUpTime X upper ω)
        (by rfl) (by rw [hup]; simp)
    simpa [hup] using h
  have hGIDown :
      IsGLB {s : ℝ≥0 | X.X s ω < lower} t := by
    have h :=
      chat03_finite_extended_infimum_isGLB
        (fun s : ℝ≥0 => X.X s ω < lower)
        (twoSidedExitDownTime X lower ω)
        (by rfl) (by rw [hdown]; simp)
    simpa [hdown] using h
  exact chat03_rightcontinuous_separated_strict_passages_no_finite_tie
    (fun s : ℝ≥0 => X.X s ω) t lower upper
    hsep (X.rightCont ω t) hGIUp hGIDown
