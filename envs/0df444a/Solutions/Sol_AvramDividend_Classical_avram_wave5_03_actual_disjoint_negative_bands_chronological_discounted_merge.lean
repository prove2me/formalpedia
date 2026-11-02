-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_disjoint_negative_bands_chronological_discounted_merge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:36:04.034357+00:00
-- url     : https://prove2.me/submissions/69f9e202-e0b2-4b78-92d3-aa1877ee5393

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ)
    (u v ζ : ℝ) (s t : ℝ≥0) (ω : Ω)
    (B₁ B₂ : Set ℝ)
    (hB₁ : B₁ ⊆ Iio (0 : ℝ)) (hB₂ : B₂ ⊆ Iio (0 : ℝ))
    (hBdisj : Disjoint B₁ B₂)
    (S₁ S₂ : Finset ℝ≥0)
    (hS₁ : ∀ r : ℝ≥0, r ∈ S₁ ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B₁)
    (hS₂ : ∀ r : ℝ≥0, r ∈ S₂ ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B₂) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let J : ℝ≥0 → ℝ := fun r =>
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
    let W : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X r ω - rightLimit D r ω
      else riskProcess X x D r ω
    let cash : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D r ω - D r ω else 0
    let A : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        if Y r ∈ Icc (u + ζ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((w (W r) - w (Function.leftLim
              (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
        else 0
      else 0
    let K : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        if Y r ∈ Icc (u + ζ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((if -1 < J r then J r * deriv w (Y r) else 0) +
              SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
        else 0
      else 0
    (∑ r ∈ S₁ ∪ S₂, A r) =
        (∑ r ∈ S₁, A r) + (∑ r ∈ S₂, A r) ∧
    (∑ r ∈ S₁ ∪ S₂, K r) =
        (∑ r ∈ S₁, K r) + (∑ r ∈ S₂, K r) ∧
    (∑ r ∈ S₁ ∪ S₂, A r) ≤
        (∑ r ∈ S₁ ∪ S₂, K r) := by
  dsimp only
  let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
  let J : ℝ≥0 → ℝ := fun r =>
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
  let W : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X r ω - rightLimit D r ω
    else riskProcess X x D r ω
  let cash : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      rightLimit D r ω - D r ω else 0
  let A : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
          ((w (W r) - w (Function.leftLim
            (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
      else 0
    else 0
  let K : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
          ((if -1 < J r then J r * deriv w (Y r) else 0) +
            SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
      else 0
    else 0
  have hdisj : Disjoint S₁ S₂ := by
    apply Finset.disjoint_left.mpr
    intro r hr₁ hr₂
    exact Set.disjoint_left.mp hBdisj
      ((hS₁ r).mp hr₁).2.2 ((hS₂ r).mp hr₂).2.2
  have hB : B₁ ∪ B₂ ⊆ Iio (0 : ℝ) := Set.union_subset hB₁ hB₂
  have hSU : ∀ r : ℝ≥0, r ∈ S₁ ∪ S₂ ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B₁ ∪ B₂ := by
    intro r
    rw [Finset.mem_union, hS₁ r, hS₂ r]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, Or.inl h.2.2⟩
      · exact ⟨h.1, h.2.1, Or.inr h.2.2⟩
    · rintro ⟨hr, hrt, hb⟩
      rcases hb with hb | hb
      · exact Or.inl ⟨hr, hrt, hb⟩
      · exact Or.inr ⟨hr, hrt, hb⟩
  have hbound : (∑ r ∈ S₁ ∪ S₂, A r) ≤
      (∑ r ∈ S₁ ∪ S₂, K r) :=
    avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
      X x D hD w hjump q u v ζ s t ω (B₁ ∪ B₂) hB
      (S₁ ∪ S₂) hSU
  exact ⟨Finset.sum_union hdisj, Finset.sum_union hdisj, hbound⟩
