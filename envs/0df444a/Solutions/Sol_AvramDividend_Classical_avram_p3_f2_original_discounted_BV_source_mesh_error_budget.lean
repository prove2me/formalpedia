-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_BV_source_mesh_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:16:56.660195+00:00
-- url     : https://prove2.me/submissions/15680d4a-8610-423f-93aa-da8a20231e5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_BV_all_Y_physical_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Almost surely, original discounted C1 mesh errors have an explicit BV source budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
        ∀ (u : ℕ → ℝ≥0) (n : ℕ),
          let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
          let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
          let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
          let z : ℕ → ℝ := fun i =>
            x + X.X (u i) ω - rightLimit D (u i) ω
          let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
          (∀ i, i < n → u i ≤ u (i + 1)) →
          (∀ i, i < n →
            Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
          (∀ i, i < n → |c i| < δ) →
          |∑ i ∈ Finset.range n,
            Real.exp (-(q * (u i : ℝ))) *
              (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
          ε * (|X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0))) := by
  filter_upwards [avram_p3_f2_original_BV_all_Y_physical_grid_variation
    X hBV] with ω hVariation
  intro ε hε
  obtain ⟨δ, hδ, hDiscounted⟩ :=
    avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
      X x C D hD w hwC1 hOpen a b hBand q hq ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u n J Y R z c hGrid hInside hSmall
  have hBound := hDiscounted ω u n hInside hSmall
  have hPhysical := hVariation u n hGrid
  exact hBound.trans
    (mul_le_mul_of_nonneg_left hPhysical (le_of_lt hε))
