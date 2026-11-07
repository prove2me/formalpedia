-- Prove2me | solution 1 for AvramDividend.Classical.avram_route6_bv_original_physical_grid_hjb_drift_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:26:11.317195+00:00
-- url     : https://prove2.me/submissions/cf6a0800-8a65-42f2-a705-8a342a528b34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- HJB drift sign on genuine active cells of a physical dividend grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (cells : Finset ℕ)
    (hregion : ∀ i ∈ cells,
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    (∑ i ∈ cells,
      Real.exp (-(q * (u i : ℝ))) *
        ((u (i + 1) : ℝ) - (u i : ℝ)) *
          (X.generator w (riskProcess X x D (u i) ω) -
            q * w (riskProcess X x D (u i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hh := (hw_gen _ (hregion i hi).1 (hregion i hi).2).2
  have hdt : (u i : ℝ) ≤ (u (i + 1) : ℝ) :=
    NNReal.coe_le_coe.mpr (hu (Nat.le_succ i))
  have hweight : 0 ≤
      Real.exp (-(q * (u i : ℝ))) *
        ((u (i + 1) : ℝ) - (u i : ℝ)) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (sub_nonneg.mpr hdt)
  exact mul_nonpos_of_nonneg_of_nonpos hweight hh
