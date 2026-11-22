-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_positive_random_clock_canonical_preruin_cash_limit_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:21:20.14746+00:00
-- url     : https://prove2.me/submissions/fb77907e-7578-4e96-a0f6-d7aefdc58153

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_cofinal_strict_reward_left_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (hq : 0 < q)
    (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      0 < ρ ω → (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω →
      Tendsto
        (fun (j : ℕ) =>
          let s : ℝ≥0 := ρ ω - ρ ω / ((j : ℝ≥0) + 1)
          Real.exp (-(q * (s : ℝ))) *
            w (x + X.X s ω - rightLimit D s ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (s : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z)))
            ∂(dividendMeasure D ω)).toReal)
        atTop
        (𝓝 (Real.exp (-(q * (ρ ω : ℝ))) *
            w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z)))
            ∂(dividendMeasure D ω)).toReal)) := by
  classical
  filter_upwards [
    avram_gclose17_original_cofinal_strict_reward_left_limit
      X hν x C D hD w hw q hq] with ω hω
  intro hρpos hρle
  let u : ℕ → ℝ≥0 := fun j =>
    ρ ω - ρ ω / ((j : ℝ≥0) + 1)
  have hCertificate :
      Monotone (fun j => (u j : ℝ)) ∧
      Tendsto (fun j => (u j : ℝ)) atTop (𝓝 (ρ ω : ℝ)) ∧
      (∀ j, (u j : ℝ) < (ρ ω : ℝ)) := by
    simpa only [u] using
      (avram_p3_grid4_contact_left_endpoint_approach_certificate
        (ρ ω) (ρ ω) hρpos hρpos)
  have hMono : Monotone u := by
    intro i j hij
    exact_mod_cast hCertificate.1 hij
  have hStrict (j : ℕ) : u j < ρ ω := by
    exact_mod_cast hCertificate.2.2 j
  have hT : Tendsto u atTop (𝓝 (ρ ω)) := by
    exact NNReal.tendsto_coe.mp hCertificate.2.1
  have hLeft : Tendsto u atTop (𝓝[<] (ρ ω)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hT, ?_⟩
    exact Filter.Eventually.of_forall (fun j => hStrict j)
  simpa only [u] using
    hω (ρ ω) hρpos hρle u hMono hStrict hLeft
