-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:00:58.489589+00:00
-- url     : https://prove2.me/submissions/dca2ff41-499e-4bac-9db9-1864c5d2ef2b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
A finite strict two-sided passage infimum has an actual first strict sampled
crossing on every sufficiently fine mesh of any positive null sequence.
No stochastic harmonicity or martingale property is required.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n) :
    ∀ᶠ n in atTop,
      ∃ k : ℕ,
        (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by
  obtain ⟨δ, hδ, hfine⟩ :=
    chat03_first_grid_strict_exit_approaches_infimum
      X ω lower upper τ hτ 1 zero_lt_one
  have hIio : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hδ
  filter_upwards [hmesh.eventually hIio] with n hn
  obtain ⟨k, _, _, hk, hkfirst⟩ := hfine (mesh n) (hpos n) hn
  exact ⟨k, hk, hkfirst⟩
