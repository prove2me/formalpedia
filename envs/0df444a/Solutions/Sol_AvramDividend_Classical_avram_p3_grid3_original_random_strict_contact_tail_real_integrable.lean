-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:49:57.734342+00:00
-- url     : https://prove2.me/submissions/bc60213a-8619-4c1e-9f7b-4264a568ca74

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine moving strict contact cash is L1 at each finite interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (τ : Ω → ℝ) (hτ : Measurable τ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτT : ∀ ω, τ ω ≤ (T : ℝ))
    (δ : ℝ) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo (τ ω - δ) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) P := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hMeas :=
    avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
      X x D hDiv q τ hτ δ
  have hFullInt :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq
      (T : ℝ) T.property
  apply hFullInt.mono' hMeas.ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    have hτnnT : (⟨τ ω, hτ0 ω⟩ : ℝ≥0) ≤ T := by
      exact_mod_cast hτT ω
    have hb :=
      avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
        X x D hDiv ω q hq T ⟨τ ω, hτ0 ω⟩ hτnnT δ
    change
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (τ ω - δ) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal at hb
    simpa [Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hb)
