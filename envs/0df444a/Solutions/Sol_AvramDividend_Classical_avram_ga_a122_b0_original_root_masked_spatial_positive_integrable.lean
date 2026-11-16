-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a122_b0_original_root_masked_spatial_positive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:19:16.358701+00:00
-- url     : https://prove2.me/submissions/7b59db29-d9a8-41c6-bbfe-bf7538b05a53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a531_finite_sum_positive_parts_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a532_original_clipped_cell_one_sided_positive_L1
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
    let U : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (∑ i ∈ Finset.range m,
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := Y s
          let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          E s * (deriv w y * z +
            (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
    ∀ m : ℕ, Integrable (fun ω =>
      if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) P := by
  classical
  intro U m
  let W : ℕ → Ω → ℝ := fun i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      if 0 < ρ ω then
        E (v (i + 1)) * (w (Z i) - w (Y (v i))) -
          (if s < ρ ω then
            E s * (deriv w (Y s) * z +
              (iteratedDeriv 2 w (Y s) / 2) *
                (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0) -
          (if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
      else 0
  have hcell := avram_ga_a532_original_clipped_cell_one_sided_positive_L1
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
    x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  have hI : Integrable
      (fun ω => max (∑ i ∈ Finset.range m, W i ω) (0 : ℝ)) P := by
    apply avram_ga_a531_finite_sum_positive_parts_integrable
    · intro i hi
      simpa only [W] using (hcell m i (Finset.mem_range.mp hi)).1
    · intro i hi
      simpa only [W] using (hcell m i (Finset.mem_range.mp hi)).2
  have hEq (ω : Ω) :
      (if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) =
      max (∑ i ∈ Finset.range m, W i ω) (0 : ℝ) := by
    by_cases hm : 0 < ρ ω
    · simp only [if_pos hm]
      congr 1
      dsimp [U,W]
      simp only [if_pos hm, Finset.sum_sub_distrib]
    · simp only [if_neg hm]
      have hz : (∑ i ∈ Finset.range m, W i ω) = 0 := by
        simp [W, hm]
      simp [hz]
  exact hI.congr (Filter.Eventually.of_forall (fun ω => (hEq ω).symm))
