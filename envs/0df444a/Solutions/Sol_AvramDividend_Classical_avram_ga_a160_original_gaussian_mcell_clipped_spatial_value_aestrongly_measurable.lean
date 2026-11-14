-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a160_original_gaussian_mcell_clipped_spatial_value_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:04:25.083654+00:00
-- url     : https://prove2.me/submissions/bdf085d3-a0cb-4e7e-bf73-8bbaa437fde2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
import Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original Gaussian stopped physical m-cell value increment sum is a.e. measurable on its positive reserve C2 domain. -/
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
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      ∑ i ∈ Finset.range m, E (i + 1) ω * (w (Z i ω) - w (Y i ω))
    ∀ m, AEStronglyMeasurable (S m) P := by
  dsimp only
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  have hObs := avram_ga_a43_original_clipped_spatial_cell_observations
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix m
  change (∀ i, Measurable (E i)) ∧
    (∀ i, Measurable (Y i)) ∧ (∀ i, Measurable (Z i)) ∧
    (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (0 < Y i ω ∧ 0 < Z i ω)) at hObs
  obtain ⟨hE,hY,hZ,hAlt⟩ := hObs
  have hAlt' (i : ℕ) (hi : i ∈ Finset.range m) :
      ∀ᵐ ω ∂P, Y i ω = Z i ω ∨
        (0 < Y i ω ∧ 0 < Z i ω) := by
    filter_upwards [hAlt] with ω hω
    have hi' : i ∈ Finset.range (m + 1) := by
      exact Finset.mem_range.mpr
        (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self m))
    rcases hω i hi' with hh | hh
    · exact Or.inl hh.2.symm
    · exact Or.inr hh
  change AEStronglyMeasurable
    (fun ω => ∑ i ∈ Finset.range m,
      E (i + 1) ω * (w (Z i ω) - w (Y i ω))) P
  exact avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
    P w (avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
      w C hTopCap hw_smooth) m Y Z (fun i ω => E (i + 1) ω)
      hY hZ (fun i => hE (i + 1)) hAlt' 
