-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:47:39.613197+00:00
-- url     : https://prove2.me/submissions/122469c1-8985-4f21-8cd4-ef4ab494d4b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_weighted_residual_mesh_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The genuine BV residual after subtracting actual source negative jumps
has favourable sign even if the next grid point crosses ruin. The mask
uses the original left-prepayment source reserve and current ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      (∑ i ∈ Finset.range n,
        (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
        else 0) * (R (u i) - R (u (i + 1)))) ≤ 0 := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    let z := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
    if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < z ∧ ENNReal.ofReal z < C then
      Real.exp (-(q * (u i : ℝ))) * deriv w z
    else 0
  have hW : ∀ ω (i : ℕ), i < n → 0 ≤ W i ω := by
    intro ω i _
    dsimp [W]
    split_ifs with hinside
    · exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (le_trans (by norm_num) (hw_grad _ hinside.2.1 hinside.2.2))
    · exact le_refl _
  exact avram_p3_bv_original_weighted_residual_mesh_nonpositive
    X hBV u n hGrid W hW
