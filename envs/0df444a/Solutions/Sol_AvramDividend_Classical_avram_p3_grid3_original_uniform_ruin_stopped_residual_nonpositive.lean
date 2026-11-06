-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:22:09.185735+00:00
-- url     : https://prove2.me/submissions/3310c9fb-3242-455e-a396-6d211c15d26c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_random_ruin_clock_residual_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let u : ℕ → ℝ≥0 := fun i =>
        ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
      let τ : Ω → ℝ≥0 := fun ξ =>
        (min (ruinTime X x D ξ) (T : ℝ≥0∞)).toNNReal
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (min (u i) (τ ω)) -
          R (min (u (i + 1)) (τ ω)))) ≤ 0 := by
  let u : ℕ → ℝ≥0 := fun i =>
    ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
  let τ : Ω → ℝ≥0 := fun ξ =>
    (min (ruinTime X x D ξ) (T : ℝ≥0∞)).toNNReal
  have hgrid : ∀ i : ℕ, i < m + 1 → u i ≤ u (i + 1) := by
    intro i hi
    exact (avram_p3_grid3_uniform_physical_clock_endpoints_monotone
      T m).2.2 (Nat.le_succ i)
  exact avram_p3_bv_original_random_ruin_clock_residual_nonpositive
    X hBV u (m + 1) hgrid τ W hW
