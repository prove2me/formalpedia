-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_linear_zero_barrier_physical_L_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:58:55.043126+00:00
-- url     : https://prove2.me/submissions/ceffe8a3-5382-4add-9ec4-ab04e4d83253

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_linear_zero_barrier_full_grid_prestate_zero
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_zero_prepayment_generator_drift_grids_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hWithin : ∀ i ∈ Finset.range (n + 1), u n i ≤ 1)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω -
        rightLimit (barrierStrategy X 0 0) t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift * deriv w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0 := by
  have hZero :=
    avram_bvb_obstruction_original_linear_zero_barrier_full_grid_prestate_zero
      X ω hDrift hPath u n hWithin
  have hGrids :=
    avram_bvb_obstruction_original_zero_prepayment_generator_drift_grids_vanish
      X 0 (barrierStrategy X 0 0) w q C u n ω hZero
  exact hGrids.2
