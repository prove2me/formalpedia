-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_source_signed_witness_to_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:50:09.680529+00:00
-- url     : https://prove2.me/submissions/5677b908-2a42-4100-b997-a67ce5596380

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_masked_original_stopped_reward_regular
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact stopped upper bound from three centred sources and signed Itô remainders. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (Mc Ms Ml G R : Ω → ℝ)
    (hMcI : Integrable Mc P) (hMsI : Integrable Ms P)
    (hMlI : Integrable Ml P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMs0 : (∫ ω, Ms ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      (if σ ω = 0 then w x else F ω) ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    (∫ ω, F ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := hw_smooth.of_le (by norm_num)
  have hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) :=
    avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
      X C hC w hw_cont hC1 hw_grad x hxc D hD
  obtain ⟨_, hMaskMeas, hMaskNonneg⟩ :=
    avram_ubv_loc6_masked_original_stopped_reward_regular
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD q σ hσstop F hFsource hFI
  have hMasked : (∫ ω, (if σ ω = 0 then w x else F ω) ∂P) ≤ w x :=
    (avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
      (fun ω => if σ ω = 0 then w x else F ω)
      Mc Ms Ml G R (w x) hMaskMeas hMaskNonneg
      hMcI hMsI hMlI hMc0 hMs0 hMl0 hG hR hIto).2
  have hzero : MeasurableSet {ω : Ω | σ ω = 0} := avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable 𝓕 σ hσstop
  have hDom : (∫ ω, F ω ∂P) ≤ ∫ ω, (if σ ω = 0 then w x else F ω) ∂P := by
    have hFamily :=
      avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
        X x q w C D hD hjump (fun _ : ℕ => σ) (fun _ : ℕ => F)
        (by intro k ω; exact hFsource ω)
        (by intro k; exact hFI)
        (by intro k; exact hzero)
    exact hFamily 0
  exact hDom.trans hMasked
