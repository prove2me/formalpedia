-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_L1_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:42:30.756149+00:00
-- url     : https://prove2.me/submissions/6c31d5a3-ff70-4b5f-b146-18b85983aea0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_horizon_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original BV left-reserve value has a finite first moment at
each physical grid time; neither generator nor raw jump L1 is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (T t : ℝ≥0) (ht : t ≤ T) :
    Integrable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P := by
  have hYjoint :=
    AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD
  have hY : Measurable (fun ω : Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
    exact hYjoint.comp (measurable_const.prodMk measurable_id)
  have hw : Measurable w :=
    (AvramDividend.Classical.local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hMeas : AEStronglyMeasurable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P :=
    (hw.comp hY).aestronglyMeasurable
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨K, hK, hbound⟩ :=
    AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_horizon_envelope
      X hBV x D hD w hw_cont hw_neg T
  have hNorm : ∀ᵐ ω ∂P,
      ‖w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)‖ ≤ K := by
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω t ht
  exact (integrable_const K).mono' hMeas hNorm
