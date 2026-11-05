-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:46:13.742204+00:00
-- url     : https://prove2.me/submissions/5704a908-cbd3-4f80-bc5b-77a23aeb1ab3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Actual original left-prestate HJB cells are retained only on the strict
pre-ruin region and strict cap interior. On a cell that can cross ruin,
its left-prestate HJB sign is still nonpositive; the separate source
jump and killed-terminal accounting remains necessary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1)) :
    ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      (∑ i ∈ Finset.range n,
        if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) ≤ 0 := by
  intro ω
  dsimp only
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hinside
  · have hgen := (hw_gen _ hinside.2.1 hinside.2.2).2
    have hdelta : 0 ≤ (u (i + 1) : ℝ) - (u i : ℝ) := by
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hGrid i (Finset.mem_range.mp hi)))
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) hgen) hdelta
  · exact le_refl _
