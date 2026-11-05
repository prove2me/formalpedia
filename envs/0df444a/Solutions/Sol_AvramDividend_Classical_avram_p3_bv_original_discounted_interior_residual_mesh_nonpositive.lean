-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:35:37.00471+00:00
-- url     : https://prove2.me/submissions/26904470-6ac4-4db8-be3b-b2a2fd7b29b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_weighted_residual_mesh_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Source-exact C¹ discount weights are activated only at strict interior
prestates. Contact with zero or cap contributes zero here and must be
handled by the separate contact/payment accounting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (Z : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range n,
        (if 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i ω)
        else 0) * (R (u i) - R (u (i + 1)))) ≤ 0 := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    if 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C then
      Real.exp (-(q * (u i : ℝ))) * deriv w (Z i ω)
    else 0
  have hW : ∀ ω (i : ℕ), i < n → 0 ≤ W i ω := by
    intro ω i hi
    dsimp [W]
    split_ifs with hinside
    · exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (le_trans (by norm_num) (hw_grad _ hinside.1 hinside.2))
    · exact le_refl _
  exact avram_p3_bv_original_weighted_residual_mesh_nonpositive
    X hBV u n hGrid W hW
