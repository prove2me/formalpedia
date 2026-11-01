-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:07:54.974914+00:00
-- url     : https://prove2.me/submissions/66a816cf-28e4-448c-abc4-dc4595b56a9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_chord_lower_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
/-- Genuine depth hazard diverges for vanishing drawdown protection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    Tendsto
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hWzero : W 0 = 0 := chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hWcont : Continuous W := scaleFunction_global_continuous_of_zero_origin X q W hW hWzero
  have hWlim : Tendsto W (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht := hWcont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ))
      simpa only [hWzero] using ht
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha
  have hlog : Tendsto (fun a : ℝ => Real.log (W a))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atBot := by
    simpa only [Function.comp_def] using
      Real.tendsto_log_nhdsGT_zero.comp hWlim
  change Tendsto K (nhdsWithin (0 : ℝ) (Ioi 0)) atTop
  apply tendsto_atTop.2
  intro M
  have hlogbound : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      Real.log (W a) ≤ Real.log (W 1) - (max M 0 + 1) :=
    tendsto_atBot.1 hlog _
  have hnear : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), a < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ))
  filter_upwards [self_mem_nhdsWithin, hnear, hlogbound] with a ha ha1 hLa
  change (0 : ℝ) < a at ha
  have hc : (Real.log (W 1) - Real.log (W a)) / (1 - a) ≤ K a :=
    avram_wave4_01_original_record_hazard_chord_lower_bound
      X q hq W hW hvar a 1 ha ha1
  have hN0 : 0 ≤ max M (0 : ℝ) + 1 := by
    linarith [le_max_right M (0 : ℝ)]
  have hMN : M ≤ max M (0 : ℝ) + 1 := by
    linarith [le_max_left M (0 : ℝ)]
  have hn : max M (0 : ℝ) + 1 ≤
      Real.log (W 1) - Real.log (W a) := by linarith
  have hn0 : 0 ≤ Real.log (W 1) - Real.log (W a) :=
    le_trans hN0 hn
  have hd0 : 0 < (1 : ℝ) - a := by linarith
  have hd1 : (1 : ℝ) - a ≤ 1 := by linarith
  have hp := mul_le_mul_of_nonneg_left hd1 hn0
  have hdiv : Real.log (W 1) - Real.log (W a) ≤
      (Real.log (W 1) - Real.log (W a)) / (1 - a) := by
    apply (le_div_iff₀ hd0).2
    nlinarith
  exact (hMN.trans hn).trans (hdiv.trans hc)
