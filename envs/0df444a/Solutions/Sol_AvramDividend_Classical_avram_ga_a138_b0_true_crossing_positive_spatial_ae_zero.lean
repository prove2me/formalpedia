-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a138_b0_true_crossing_positive_spatial_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:07:21.501808+00:00
-- url     : https://prove2.me/submissions/d56abfad-e5c8-4478-8ff2-c3e23dc94e12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a383_true_crossing_positive_part_mesh_identity_v2
import Theorems.Thm_AvramDividend_Classical_avram_ga_a382_b0_true_crossing_cell_uniform_positive_bound_v2
import Theorems.Thm_AvramDividend_Classical_avram_ga_a141_original_gaussian_random_crossing_uniform_positive_cell_limit
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
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
    let Cross : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let Ccell : ℕ → ℝ := fun i =>
      E (ρ ω) * (w (Y (s i) +
        (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ ρ ω < s i + Δ then Ccell i else 0
    ∀ᵐ ω ∂P, Tendsto (fun m => max (Cross m ω) 0)
      atTop (nhds (0 : ℝ)) := by
  classical
  let F : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun k => X.X (s k + Δ) ω - X.X (s k) ω
    let Z : ℕ → ℝ := fun k => R k - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun k =>
      E (s k) * (deriv w (Y (s k)) * Z k +
        (iteratedDeriv 2 w (Y (s k)) / 2) *
          (Z k^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s k) * X.generator w (Y (s k))
    E (ρ ω) * (w (Y (s i) +
      (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
  obtain ⟨B, hB0, hBound, hBae⟩ :=
    avram_ga_a382_b0_true_crossing_cell_uniform_positive_bound_v2
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  let f : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if ρ ω < ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) then F m i ω else 0
  have hb : ∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
      ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
      max (f m i ω) 0 ≤ B m ω := by
    intro m ω i hi hs he
    by_cases hc : ρ ω < ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
    · change max (if ρ ω < ((Nat.succ i : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) then F m i ω else 0) 0 ≤ B m ω
      simpa only [if_pos hc] using hBound m ω i hi hs he
    · change max (if ρ ω < ((Nat.succ i : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) then F m i ω else 0) 0 ≤ B m ω
      simpa only [if_neg hc, max_self] using hB0 m ω
  have hMain := avram_ga_a141_original_gaussian_random_crossing_uniform_positive_cell_limit
    P n ρ f B hB0 hb hBae
  change ∀ᵐ ω ∂P, Tendsto (fun m =>
    max (∑ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      if (i : ℝ≥0) * Δ < ρ ω ∧ ρ ω < (i : ℝ≥0) * Δ + Δ
      then F m i ω else 0) 0) atTop (nhds (0 : ℝ))
  filter_upwards [hMain] with ω hω
  have heq (m : ℕ) :
      max (∑ i ∈ Finset.range m,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        if (i : ℝ≥0) * Δ < ρ ω ∧ ρ ω < (i : ℝ≥0) * Δ + Δ
        then F m i ω else 0) 0 =
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω ∧
            ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
              ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
        then max (f m i ω) 0 else 0 := by
    have hn' : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    exact avram_ga_a383_true_crossing_positive_part_mesh_identity_v2
      m ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) (ρ ω)
      (div_pos hn' (by positivity)) (fun i => F m i ω)
  exact hω.congr' (Filter.Eventually.of_forall (fun m => (heq m).symm))
