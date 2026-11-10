-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf14_original_infinite_stopped_centered_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:16:26.360855+00:00
-- url     : https://prove2.me/submissions/a9163aa7-b783-46fe-92d9-e60e34d29168
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_exact_clock_zero_reward_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf16_original_positive_clock_centered_source_witness
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Positive-clock original stopped source plus proved zero atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k, ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, σ k ω = 0 → M ω = 0) ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + M ω) := by
  intro k
  obtain ⟨M, hMI, hMean, hZero, hPos⟩ :=
    avram_mix_inf16_original_positive_clock_centered_source_witness
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop σ F
      hσstop hσle hFsource hFI hInfiniteActivity k
  refine ⟨M, hMI, hMean, hZero, ?_⟩
  filter_upwards [hZero, hPos] with ω hZeroAt hPosAt
  by_cases hz : σ k ω = 0
  · rw [hZeroAt hz]
    simpa only [add_zero] using
      (avram_p4_f8_original_exact_clock_zero_reward_le_initial
        X x q w C D hD hjump σ F hFsource k ω hz)
  · exact hPosAt hz
