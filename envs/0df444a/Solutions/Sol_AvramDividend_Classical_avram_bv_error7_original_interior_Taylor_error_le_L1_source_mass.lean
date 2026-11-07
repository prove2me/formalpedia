-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:00:16.925471+00:00
-- url     : https://prove2.me/submissions/7cf5f95f-f01a-4a5b-b900-c626c5ce0532

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Source-exact stopped interior C1 errors are controlled by a fixed
multiple of the original X_T first-moment variation envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
          u 0 = 0 → u n = T →
          (∀ i, i < n → u i ≤ u (i + 1)) →
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
            else 0
           let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
           let z : ℕ → ℝ := fun i =>
             x + X.X (u i) ω - rightLimit D (u i) ω
           let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
           (∀ i, i < n →
             Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
           (∀ i, i < n → |c i| < δ) →
           |∑ i ∈ Finset.range n,
             Real.exp (-(q * (u i : ℝ))) *
               (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
             ε * (|X.drift| * (T : ℝ) +
               |(T : ℝ) * X.drift - X.X T ω|)) := by
  intro ε hε
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
      X x C D hD w hwC1 hOpen a b hBand q hq ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards
    [avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
      X hBV T] with ω hVar
  intro u n hu0 hun hmono
  dsimp
  intro hCells hSmall
  exact (hTaylor ω u n hCells hSmall).trans
    (mul_le_mul_of_nonneg_left (hVar u n hu0 hun hmono)
      (le_of_lt hε))
