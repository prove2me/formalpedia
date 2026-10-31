-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_canonical_infinite_jump_log_rate_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:54:51.021133+00:00
-- url     : https://prove2.me/submissions/9a1af515-064a-4c69-bf7d-4d883fa9555f

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The genuine discounted upward-record log hazard is continuous in
reflected ruin depth under the canonical infinite small-jump hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      -Real.log ((∫⁻ ω,
        if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal)) (Ioi 0) := by
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hjump
  exact avram_wave3_01_original_record_log_rate_continuous
    X q hq W hW hnbv hjump
