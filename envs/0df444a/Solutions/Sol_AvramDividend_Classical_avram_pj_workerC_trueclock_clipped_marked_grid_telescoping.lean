-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:23:07.688949+00:00
-- url     : https://prove2.me/submissions/463b7472-72aa-46fa-b4dd-04d39e4a66e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ρ : Ω → ℝ≥0) (n m : ℕ)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (B : Set ℝ) (hB : MeasurableSet B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (I ×ˢ B)
    (∑ i ∈ Finset.range (m + 1), J (Ioc (u i) (u (i + 1)))) =
      J (Ioc 0 (ρ ω)) := by
  intro Δ u J
  have hMono : Monotone u := by
    simpa [u, Δ] using
      (AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone
        (n : ℝ≥0) (ρ ω) m)
  have hZero : u 0 = 0 := by simp [u, Δ]
  have hEnd : u (m + 1) = ρ ω := by
    have hTerminal :=
      (AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_endpoints_monotone
        (n : ℝ≥0) m).2.1
    change min (((min (m + 1) (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω) = ρ ω
    have hT : (((min (m + 1) (m + 1) : ℕ) : ℝ≥0) * Δ) =
        (n : ℝ≥0) := by simpa [Δ] using hTerminal
    rw [hT]
    exact min_eq_right (hρbound ω)
  have hPart :=
    AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_grid_telescoping
      X ω u (fun i => hMono (Nat.le_succ i)) hZero B hB (m + 1)
  simpa only [hEnd] using hPart

