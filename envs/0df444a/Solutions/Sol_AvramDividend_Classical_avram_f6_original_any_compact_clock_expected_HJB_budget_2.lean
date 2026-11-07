-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_any_compact_clock_expected_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:22:28.631472+00:00
-- url     : https://prove2.me/submissions/6e4a2f58-d1d8-40fa-b238-e15eceab328a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f7_original_any_compact_clock_ito_signed_source_witnesses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hStop : (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))))
    (hBound : (∀ k ω, σ k ω ≤ τ ω))
    (hExact : (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨
                (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal))
    (hMeas : (∀ k, Measurable (F k)))
    (hInt : (∀ k, Integrable (F k) P))
    (hNonneg : (∀ k, 0 ≤ᵐ[P] F k)) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨M, G, H, hMI, hGI, hHI, hMzero, hGHsign, hFM⟩ :=
    avram_f7_original_any_compact_clock_ito_signed_source_witnesses
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
      σ F hStop hBound hExact hMeas hInt hNonneg k
  have hGHInt : Integrable (fun ω => G ω + H ω) P := hGI.add hHI
  have hGMInt : Integrable (fun ω => w x + M ω) P :=
    (integrable_const (w x)).add hMI
  have hTotalInt :
      Integrable (fun ω => (w x + M ω) + (G ω + H ω)) P :=
    hGMInt.add hGHInt
  have hFM' : ∀ᵐ ω ∂P,
      F k ω ≤ (w x + M ω) + (G ω + H ω) := by
    filter_upwards [hFM] with ω hω
    simpa only [add_assoc] using hω
  have hFirst := integral_mono_ae (hInt k) hTotalInt hFM'
  have hFirst' :
      (∫ ω, F k ω ∂P) ≤
          (∫ ω, w x + M ω ∂P) + (∫ ω, G ω + H ω ∂P) := by
    simpa only [integral_add hGMInt hGHInt] using hFirst
  have hMeanGM : (∫ ω, w x + M ω ∂P) = w x := by
    rw [integral_add (integrable_const (w x)) hMI]
    simp only [hMzero, add_zero]
    simp
  have hGHnonpos : (∫ ω, G ω + H ω ∂P) ≤ 0 := by
    have hcmp := integral_mono_ae hGHInt (integrable_const (0 : ℝ)) hGHsign
    simpa using hcmp
  rw [hMeanGM] at hFirst'
  linarith
