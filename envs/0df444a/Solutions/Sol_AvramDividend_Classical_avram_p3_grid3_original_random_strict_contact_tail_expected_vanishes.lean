-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:53:07.128051+00:00
-- url     : https://prove2.me/submissions/e9d926e9-3ccf-4138-a8a4-f14fa7fded6b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stochastic strict contact cash converges to zero in expected real value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (τ : Ω → ℝ) (hτ : Measurable τ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτT : ∀ ω, τ ω ≤ (T : ℝ))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo (τ ω - δ n) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo (τ ω - δ n) (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let G : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  have hGInt : Integrable G P := by
    simpa only [G] using
      avram_p3_bv_original_strict_cash_L1 X x C D hD q hq
        (T : ℝ) T.property
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) P := by
    have hm := avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
      X x D hDiv q τ hτ (δ n)
    simpa only [F] using hm.ennreal_toReal.aestronglyMeasurable
  have hBound (n : ℕ) : ∀ᵐ ω ∂P, ‖F n ω‖ ≤ G ω :=
    Filter.Eventually.of_forall (fun ω => by
      have hτnnT : (⟨τ ω, hτ0 ω⟩ : ℝ≥0) ≤ T := by
        exact_mod_cast hτT ω
      have hb :=
        avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
          X x D hDiv ω q hq T ⟨τ ω, hτ0 ω⟩ hτnnT (δ n)
      change F n ω ≤ G ω at hb
      have hnn : 0 ≤ F n ω := ENNReal.toReal_nonneg
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using hb)
  have hLim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (0 : ℝ)) :=
    Filter.Eventually.of_forall (fun ω => by
      have hτnnT : (⟨τ ω, hτ0 ω⟩ : ℝ≥0) ≤ T := by
        exact_mod_cast hτT ω
      have ht :=
        avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
          X x D hDiv ω q hq T ⟨τ ω, hτ0 ω⟩ hτnnT
          δ hδpos hδanti hδ
      change Tendsto (fun n => F n ω) atTop (𝓝 (0 : ℝ)) at ht
      exact ht)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      G hMeas hGInt hBound hLim
  simpa only [F, integral_zero] using hDCT
