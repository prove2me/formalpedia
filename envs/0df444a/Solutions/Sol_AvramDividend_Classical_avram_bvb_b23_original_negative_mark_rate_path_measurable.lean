-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b23_original_negative_mark_rate_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:42:50.0722+00:00
-- url     : https://prove2.me/submissions/84a8f105-b17f-4b92-bb94-3971addce4a4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_prepayment_leftlim_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_zero_negative_measurable
import Mathlib.MeasureTheory.Integral.Prod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (ν : Measure ℝ) [SFinite ν] (ω : Ω) :
    Measurable (fun t : ℝ≥0 =>
      ∫ z, w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t + z) -
        w (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ∂ν) := by
  classical
  let U : ℝ≥0 → ℝ := fun t =>
    Function.leftLim (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
  have hU : Measurable U :=
    avram_bvb_b22_original_prepayment_leftlim_path_measurable X x D hD ω
  have hw : Measurable w :=
    avram_p3_bv_original_zero_negative_measurable w hw_cont hw_neg
  have hF : Measurable (fun p : ℝ≥0 × ℝ =>
      w (U p.1 + p.2) - w (U p.1)) :=
    (hw.comp ((hU.comp measurable_fst).add measurable_snd)).sub
      (hw.comp (hU.comp measurable_fst))
  have hIntegral :
      Measurable (fun t : ℝ≥0 =>
        ∫ z, w (U t + z) - w (U t) ∂ν) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  exact hIntegral
