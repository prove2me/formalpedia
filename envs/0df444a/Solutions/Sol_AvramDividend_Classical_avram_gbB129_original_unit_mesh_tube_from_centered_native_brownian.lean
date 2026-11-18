-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:47:33.474914+00:00
-- url     : https://prove2.me/submissions/4f6d5509-c693-4b50-b385-52f30e8d7004

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The centred Brownian tube controls every actual fine original-grid endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hSource : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B u ω + 2 * (u : ℝ))
    (hc : X.c = 2)
    (hCentered : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      |B u ω| ≤ (1 / 4000 : ℝ))
    (m : ℕ) (hm : 15999 ≤ m) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    ∀ i : ℕ, s i ≤ (1 / 1000 : ℝ≥0) + Δ →
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ (1 / 4000 : ℝ)
    := by
  dsimp
  intro i hi
  have hΔ :=
    avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot m hm
  have htime :
      ((i : ℝ≥0) * ((1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ≤
        (17 / 16000 : ℝ≥0) := by
    calc
      _ ≤ (1 / 1000 : ℝ≥0) +
          ((1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) := hi
      _ ≤ (1 / 1000 : ℝ≥0) + (1 / 16000 : ℝ≥0) := by
        simpa only [add_comm] using (add_le_add_left hΔ (1 / 1000 : ℝ≥0))
      _ = (17 / 16000 : ℝ≥0) := by norm_num
  have heq :
      X.X ((i : ℝ≥0) *
          ((1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω -
        (((i : ℝ≥0) * ((1 : ℝ≥0) /
          ((m + 1 : ℕ) : ℝ≥0))) : ℝ) * X.c =
      B ((i : ℝ≥0) *
          ((1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω := by
    rw [hSource _ htime, hc]
    push_cast
    ring
  calc
    _ = |B ((i : ℝ≥0) *
          ((1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω| := congrArg abs heq
    _ ≤ (1 / 4000 : ℝ) := hCentered _ htime
