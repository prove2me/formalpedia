-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_zero_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:12:24.056854+00:00
-- url     : https://prove2.me/submissions/3c17097c-1999-40a6-9109-d61a222efc7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- A vanishing positive drawdown allowance kills each fixed-height record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (h : ℝ) (hh : 0 < h) :
    Tendsto
      (fun a : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) := by
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hK : Tendsto K (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
      X q hq W hW hvar
  have hm : Tendsto (fun a : ℝ => h * K a)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hh).2 hK
  have hexp : Tendsto (fun a : ℝ => Real.exp (-(h * K a)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
  have heq :
      (fun a : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun a : ℝ => Real.exp (-(h * K a))) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    simpa only [K, neg_mul] using
      (avram_wave4_01_original_record_exponential_hazard
        X q hq W hW hvar a ha h hh)
  exact hexp.congr' heq.symm
