-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a536_source_spatial_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:15:55.95039+00:00
-- url     : https://prove2.me/submissions/7fbfd55c-790c-4e25-9d64-3338f2ce3841

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a553_original_clipped_spatial_positive_exponential_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a549_original_spatial_discounted_diff_AEStronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_gledger71_original_clipped_source_joint_measurability
import Theorems.Thm_AvramDividend_Classical_avram_gledger69_original_clipped_source_cell_exponential_L1
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
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      if 0 < ρ ω then E (v (i + 1)) * (w (Z i) - w (Y (v i))) else 0
    ∀ m i : ℕ, i < m →
      Integrable (fun ω => max (A m i ω) (0 : ℝ)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro A m i hi
  obtain ⟨θ,K,L,hθ,hK,hL,hEnvelope⟩ :=
    avram_ga_a553_original_clipped_spatial_positive_exponential_majorant
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun k ω => min ((k : ℝ≥0) * Δ) (ρ ω)
  let Z : Ω → ℝ := fun ω =>
    x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  have hMeas :=
    avram_ga_a549_original_spatial_discounted_diff_AEStronglyMeasurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m i hi
  have hpack := avram_gledger71_original_clipped_source_joint_measurability
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix m
  have hd0 : ∀ (u : ℝ≥0) (ω : Ω),
      0 ≤ rightLimit D (min (u * Δ) (ρ ω)) ω := by
    intro u ω
    exact avram_ga_a35_original_dividend_rightLimit_nonnegative
      D hD.1.1 _ _
  have hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P := by
    have he := avram_gledger69_original_clipped_source_cell_exponential_L1
      X θ hθ x D Δ (n : ℝ≥0) ρ hpack.2.2.2.2.2
      hpack.2.2.1 hpack.2.2.2.1 hd0 (hpack.2.1 θ)
    simpa only [Z,v,Δ] using he i
  have hdom : Integrable
      (fun ω => K * Real.exp (θ * Z ω) + L) P :=
    (hExp.const_mul K).add (integrable_const L)
  have hMeasPos : AEStronglyMeasurable
      (fun ω => max (A m i ω) (0 : ℝ)) P :=
    (hMeas.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  apply hdom.mono_nonneg hMeasPos
    (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  filter_upwards [hEnvelope m i hi] with ω hω
  simpa only [Z,v,Δ] using hω
