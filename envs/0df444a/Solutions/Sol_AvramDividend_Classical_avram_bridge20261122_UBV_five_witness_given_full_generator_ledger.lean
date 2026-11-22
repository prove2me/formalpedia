-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261122_UBV_five_witness_given_full_generator_ledger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:44:24.958704+00:00
-- url     : https://prove2.me/submissions/ed01b120-dbb4-45f7-aa84-434e7deb95d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_ito_source_given_trueband_countable_stopped_martingale
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- Definitionally the genuine original pre-right-dividend surplus at p.1. -/
private abbrev avramBridgePhysicalUpre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (p : ℝ≥0 × Ω) : ℝ :=
  Function.leftLim (fun s : ℝ≥0 =>
    x + X.X s p.2 - rightLimit D s p.2) p.1

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
    (hSourceGeneratorSplit : ∀ (T : ℝ≥0) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) (E : Set (ℝ≥0 × Ω)) (hE : MeasurableSet[𝓕.rightCont.predictable] E) (hG : IntegrableOn (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then Real.exp
    (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w (avramBridgePhysicalUpre X x D p))) E μ) (hJ :
    IntegrableOn (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.c * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 -
    rightLimit D s p.2) p.1) + (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w (avramBridgePhysicalUpre X x D p) z ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x +
    X.X s p.2 - rightLimit D s p.2) p.1))) E μ), (∫ p in E, (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.generator w (Function.leftLim (fun s : ℝ≥0 =>
    x + X.X s p.2 - rightLimit D s p.2) p.1) - q * w (avramBridgePhysicalUpre X x D p)) ∂μ) = (∫ p in E, (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤ ruinTime X x
    D p.2 then (1 : ℝ) else 0) else 0) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w (avramBridgePhysicalUpre X x D p)) ∂μ) + (∫ p in E, (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 :
    ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.c * deriv w (avramBridgePhysicalUpre X x D p) + (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w
    (avramBridgePhysicalUpre X x D p) z ∂X.ν) - q * w (avramBridgePhysicalUpre X x D p)) ∂μ) ) (hSourceResidualIntegrable : ∀ (T : ℝ≥0) (μ :
    @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) (E : Set (ℝ≥0 × Ω)) (hE : MeasurableSet[𝓕.rightCont.predictable] E) (hG : IntegrableOn (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤
    ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w (avramBridgePhysicalUpre X x D p))) E μ) (hJ : IntegrableOn (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
    Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.c * deriv w (avramBridgePhysicalUpre X x D p) + (∫ z in Iio (0 : ℝ),
    SpectrallyNegativeLevy.generatorIntegrand w (avramBridgePhysicalUpre X x D p) z ∂X.ν) - q * w (avramBridgePhysicalUpre X x D p))) E μ),
    IntegrableOn (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) * (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) else 0) * (X.generator w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 -
    rightLimit D s p.2) p.1) - q * w (avramBridgePhysicalUpre X x D p))) E μ )
    (hSourceFiniteGridSplit : ∀ {ι : Type*} (T : ℝ≥0)
          (S : Finset ι) (t : ι → ℝ≥0) (ω : Ω),
          let y : ι → ℝ := fun i => Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (t i)
          let k : ι → ℝ := fun i =>
            if t i ≤ T then
              (if (t i : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0) else 0
          (∑ i ∈ S,
            k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
              (X.generator w (y i) - q * w (y i)))) =
            (∑ i ∈ S,
              k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
                (X.σ ^ 2 / 2 * iteratedDeriv 2 w (y i)))) +
            (∑ i ∈ S,
              k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
                (X.c * deriv w (y i) +
                  (∫ z in Iio (0 : ℝ),
                    SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) -
                    q * w (y i))))
    ) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω)    := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  refine
    avram_mathfin22_original_ito_source_given_trueband_countable_stopped_martingale
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI ?_
  intro K a b hab σ hσ hσBound hσCount
  exact
    avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero
      X K a b hab σ hσ hσBound hσCount
