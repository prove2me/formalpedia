-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_zero_prepayment_generator_drift_grids_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:52:31.935645+00:00
-- url     : https://prove2.me/submissions/3de60475-1b3c-4178-aa68-62cf71ff71a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω)
    (hZero : ∀ i ∈ Finset.range (n + 1),
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n i) = 0) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0 ∧
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift * deriv w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0 := by
  dsimp
  constructor
  all_goals
    apply Finset.sum_eq_zero
    intro i hi
    have hz := hZero i hi
    simp [hz]
