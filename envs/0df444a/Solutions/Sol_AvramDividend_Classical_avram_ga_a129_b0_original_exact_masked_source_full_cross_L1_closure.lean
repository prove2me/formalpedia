-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a129_b0_original_exact_masked_source_full_cross_L1_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:25.665662+00:00
-- url     : https://prove2.me/submissions/7acf642a-8319-4dd2-90f9-30bcf759263d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a125_original_gaussian_masked_full_cross_positive_expected_L1_glue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original Gaussian b0 positive-spatial masked expectation is squeezed by the genuine full and crossing source budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    let U : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
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
    let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) * (deriv w (Y (s i)) * Z i +
      (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let F : ℕ → ℝ := fun i => E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    let Cross : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) * (deriv w (Y (s i)) * Z i +
      (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let Ccell : ℕ → ℝ := fun i => E (ρ ω) * (w (Y (s i) +
      (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ ρ ω < s i + Δ then Ccell i else 0

    (∀ m, Integrable (fun ω => if 0 < ρ ω then max (U m ω) 0 else 0) P) →
    (∀ m, Integrable (fun ω => |Full m ω|) P) →
    (∀ m, Integrable (fun ω => max (Cross m ω) 0) P) →
    Tendsto (fun m => ∫ ω, |Full m ω| ∂P) atTop (nhds (0 : ℝ)) →
    Tendsto (fun m => ∫ ω, max (Cross m ω) 0 ∂P) atTop (nhds (0 : ℝ)) →
    Tendsto (fun m => ∫ ω,
      (if 0 < ρ ω then max (U m ω) 0 else 0) ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  dsimp only
  intro hUI hFI hCI hFT hCT
  have hSplit (m : ℕ) (ω : Ω) :=
    avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
      X x D w q ω n m (ρ ω)
  exact avram_ga_a125_original_gaussian_masked_full_cross_positive_expected_L1_glue
    P _ _ _ (fun ω => 0 < ρ ω) hSplit hUI hFI hCI hFT hCT
