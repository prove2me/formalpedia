-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_prepayment_caplinear_defect_supported_abovecap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:26:19.730219+00:00
-- url     : https://prove2.me/submissions/b885d6e3-c0ff-438c-8f3a-0d25aeef809d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c q : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (v : ℕ → ℝ≥0) (m : ℕ) (w V : ℝ → ℝ)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c)) :
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range m,
      Real.exp (-(q * (v (i + 1) : ℝ))) * (V (Z i) - w (Z i))) =
    (∑ i ∈ Finset.range m,
      if c < Z i then
        Real.exp (-(q * (v (i + 1) : ℝ))) *
          (w c + (Z i - c) - w (Z i))
      else 0) := by
  dsimp only
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : c < x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
  . have hnot : ¬ x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ≤ c := not_le.mpr h
    simp [hV, h, hnot]
  . have hle : x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ≤ c := le_of_not_gt h
    simp [hV, h, hle]
