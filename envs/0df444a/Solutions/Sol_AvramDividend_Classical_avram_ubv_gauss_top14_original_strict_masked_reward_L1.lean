-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss_top14_original_strict_masked_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:15:51.227845+00:00
-- url     : https://prove2.me/submissions/962ee06a-56e5-499b-8d06-5eee71a44d13

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ k ω, σ k ω ≤ T) :
    ∀ k, Integrable (fun ω =>
      if σ k ω = 0 then w x else
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by
  have hσmeas : ∀ k, Measurable (fun ω : Ω => (σ k ω : ℝ)) := by
    intro k
    have hENN : Measurable (fun ω : Ω => (σ k ω : WithTop ℝ≥0)) :=
      (hσstop k).measurable'
    exact (measurable_coe_nnreal_ennreal_iff.mp hENN).coe_nnreal_real
  have hCash :=
    avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
      X x C D hD q (le_of_lt hq) T σ hσmeas hσbound
  intro k
  have hTerm :=
    avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
      X hX hBV hNuZero q hq w C hC hTopCap hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad x D hD
      (σ k) (hσstop k) T (hσbound k)
  have hSet : MeasurableSet {ω : Ω | σ k ω = 0} := by
    have hENN : Measurable (fun ω : Ω => (σ k ω : WithTop ℝ≥0)) :=
      (hσstop k).measurable'
    have hNN : Measurable (σ k) :=
      measurable_coe_nnreal_ennreal_iff.mp hENN
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : ℝ≥0)).preimage hNN
  have hPiece : Integrable
      ({ω : Ω | σ k ω = 0}.piecewise (fun _ => w x)
        (fun ω => Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)) P := by
    letI : IsProbabilityMeasure P := X.isProbability
    classical
    exact Integrable.piecewise hSet
      (integrable_const (w x)).integrableOn
      (hTerm.add (hCash.2.1 k)).integrableOn
  change Integrable (fun ω =>
    if σ k ω = 0 then w x else
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P at hPiece
  exact hPiece