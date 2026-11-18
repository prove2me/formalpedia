-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:51:07.176853+00:00
-- url     : https://prove2.me/submissions/22bcf693-80b9-4313-b497-1c2ea4f9aeb1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB118_original_uniform_physical_grid_monotone_step
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
noncomputable section
/-- A single Gaussian tube controls original reserve, stopping clock and grid noise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hSource : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B u ω + 2 * (u : ℝ))
    (hc : X.c = 2) (hX0 : X.X 0 ω = 0)
    (hCentered : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      |B u ω| ≤ (1 / 4000 : ℝ))
    (hDrifted : ∀ u : ℝ≥0, u ≤ (1 / 1000 : ℝ≥0) →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (m : ℕ) (hm : 15999 ≤ m) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    (∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      (5 / 44 : ℝ) < riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω) ∧
    sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
      (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
        Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)}) =
      (1 / 1000 : ℝ≥0) ∧
    |(Finset.range (m + 1)).sum (fun i =>
      if s i < (1 / 1000 : ℝ≥0) then
        Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ (1 / 4000 : ℝ) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact avram_gbB38_barrier_reserve_above_cutoff_on_tube
      X t ω (fun u hu => hDrifted u (hu.trans ht))
  · exact avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
      X (1 / 1000 : ℝ≥0) ω hDrifted
  · let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    obtain ⟨hsRaw, hs0Raw, hstepRaw⟩ :=
      avram_gbB118_original_uniform_physical_grid_monotone_step 1 m
    have hs : Monotone s := by
      simpa [s, Δ] using hsRaw
    have hs0 : s 0 = 0 := by
      simpa [s, Δ] using hs0Raw
    have hstep : ∀ i, s (i + 1) = s i + Δ := by
      intro i
      simpa [s, Δ] using hstepRaw i
    have hTube : ∀ i, s i ≤ (1 / 1000 : ℝ≥0) + Δ →
        |X.X (s i) ω - (s i : ℝ) * X.c| ≤ (1 / 4000 : ℝ) := by
      simpa [s, Δ] using
        (avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
          X ω B hSource hc hCentered m hm)
    have hnoise :=
      avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
        X ω m s hs hs0 Δ (1 / 1000 : ℝ≥0) hstep
        hX0 (1 / 100 : ℝ) (1 / 4000 : ℝ)
        (by norm_num) (by norm_num) hTube
    simpa [s, Δ] using hnoise
