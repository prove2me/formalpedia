-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_controlled_prejump_small_jump_taylor_kernel_predictable_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:42:42.445219+00:00
-- url     : https://prove2.me/submissions/884eadf0-cbef-4fc9-9b5b-40c5d60c8d19

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_corrected_value_global_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_marked_value_increment_measurable_of_process_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The actual pre-jump Taylor remainder has a predictable mark-measurable kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable[(𝓕.rightCont.predictable).prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ =>
        let a := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s z.1.2 - rightLimit D s z.1.2)
          z.1.1
        let d := if 0 < a ∧ ENNReal.ofReal a < C then deriv w a else 0
        w (a + z.2) - w a - d * z.2) := by
  let U : ℝ≥0 × Ω → ℝ := fun z =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s z.2 - rightLimit D s z.2) z.1
  have hPred : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable] U at hPred
  have hU : Measurable[𝓕.rightCont.predictable] U := hPred.measurable
  have hw := avram_wave4_04b_corrected_value_global_measurable
    w hw_cont hw_neg
  have hInc : Measurable[(𝓕.rightCont.predictable).prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ =>
        w (U z.1 + z.2) - w (U z.1)) :=
    avram_wave4_04b_marked_value_increment_measurable_of_process_measurable
      (𝓕.rightCont.predictable) U hU w hw
  have hderiv :=
    avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
      w C hw_smooth
  have hUB : Measurable[(𝓕.rightCont.predictable).prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ => U z.1) :=
    hU.comp measurable_fst
  have hD : Measurable[(𝓕.rightCont.predictable).prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ =>
        (if 0 < U z.1 ∧ ENNReal.ofReal (U z.1) < C
        then deriv w (U z.1) else 0) * z.2) :=
    (hderiv.comp hUB).mul measurable_snd
  exact hInc.sub hD
