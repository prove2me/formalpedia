-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_physical_grid_drift_residual_ae_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:38:07.579586+00:00
-- url     : https://prove2.me/submissions/21523ac4-622c-469a-88e3-77a22eff294f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (B : Ω → ℝ)
    (hB : ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      B ω =
        (∑ i ∈ Finset.range n,
          if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u (i + 1) : ℝ) - (u i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range n,
           (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
           else 0) * (R (u i) - R (u (i + 1))))) :
    ∀ᵐ ω ∂P, B ω ≤ 0 := by
  classical
  have hGenerator := avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
    X x C D w q hw_gen u n hGrid
  have hResidual := avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
    X hBV x C D w q hw_grad u n hGrid
  filter_upwards [hResidual] with ω hω
  have hG := hGenerator ω
  have hBω := hB ω
  dsimp only at hG hω hBω
  linarith only [hBω, hG, hω]
