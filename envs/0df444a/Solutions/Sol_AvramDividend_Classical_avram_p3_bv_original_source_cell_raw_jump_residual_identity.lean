-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_source_cell_raw_jump_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:07:27.118857+00:00
-- url     : https://prove2.me/submissions/2b04b330-be00-441e-8118-d5c166424b9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The actual frozen-dividend original source cell is exactly drift,
   the full raw negative-jump interval, and the continuous BV residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (i : ℕ),
      u i ≤ u (i + 1) →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        (t : ℝ) * X.drift - X.X t ω - J t
      let Y : ℝ≥0 → ℝ := fun t =>
        x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun j =>
        x + X.X (u (j + 1)) ω - rightLimit D (u j) ω
      Z i = Y (u i) +
        ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift -
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0) -
        (R (u (i + 1)) - R (u i)) := by
  filter_upwards [
    avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle
      X hBV] with ω hω
  intro u i hui
  have hRaw := hω (u i) (u (i + 1)) hui
  dsimp at hRaw ⊢
  linear_combination hRaw
