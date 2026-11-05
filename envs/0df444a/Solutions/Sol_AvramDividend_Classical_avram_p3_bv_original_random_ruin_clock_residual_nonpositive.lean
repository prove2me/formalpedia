-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_random_ruin_clock_residual_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:30:19.582791+00:00
-- url     : https://prove2.me/submissions/70b105e1-8396-4a48-8c3e-628362c31aca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The actual original BV continuous residual remains a nonpositive
weighted correction on sample-dependent ruin-clamped grid times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (τ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)
      (∑ i ∈ Finset.range n,
        W i ω * (R (min (u i) (τ ω)) -
          R (min (u (i + 1)) (τ ω)))) ≤ 0 := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV]
    with ω hR
  dsimp only
  apply Finset.sum_nonpos
  intro i hi
  have hClock : min (u i) (τ ω) ≤ min (u (i + 1)) (τ ω) :=
    min_le_min (hGrid i (Finset.mem_range.mp hi)) le_rfl
  exact mul_nonpos_of_nonneg_of_nonpos (hW ω i)
    (sub_nonpos.mpr (hR hClock))
