-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:40:39.705396+00:00
-- url     : https://prove2.me/submissions/c04b57fd-1448-4f13-a603-8cda8f8430aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB118_original_uniform_physical_grid_monotone_step
import Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact original uniform stopped Gaussian mesh is bounded on its tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n m : ℕ) (T : ℝ≥0)
    (hX0 : X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    (∀ i, s i ≤ T + Δ →
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) →
    |(Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ ε := by
  dsimp
  intro hTube
  obtain ⟨hs, hs0, hstep⟩ :=
    avram_gbB118_original_uniform_physical_grid_monotone_step n m
  exact avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
    X ω m
    (fun i => (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))
    hs hs0
    ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
    T hstep hX0 q ε hq hε hTube
