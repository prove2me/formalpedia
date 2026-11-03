-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_cadlag_strict_downjumps_countably_rational_enumerable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:48:05.37124+00:00
-- url     : https://prove2.me/submissions/ec49cf32-4b87-44d2-af17-a6e397ec304f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every strict downward jump appears at an exact measurable rational first-hit time. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hDown : ∀ u : ℝ≥0, 0 < u →
      Y u - Function.leftLim Y u ≠ 0 →
      Y u < Function.leftLim Y u)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    let T : ℕ → ℝ≥0 := fun k =>
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧
          Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal
    ∀ u : ℝ≥0, 0 < u →
      Y u - Function.leftLim Y u ≠ 0 →
      ∃ k : ℕ, T k = u := by
  dsimp only
  intro u hu hj
  have hlt : Y u < Function.leftLim Y u := hDown u hu hj
  obtain ⟨a, s, b, hsu, hub, hL, hR⟩ :=
    avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
      Y u hu hlt (hLeft u hu) (hRight u)
  obtain ⟨v, ⟨m, rfl⟩, hm⟩ := hdense.exists_between hsu
  have hI :=
    avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing
      Y grid hdense s u b (a : ℝ) hsu hub hL hR m hm
  obtain ⟨k, hk⟩ := hpairs (m, a)
  refine ⟨k, ?_⟩
  rw [hk]
  convert congrArg ENNReal.toNNReal hI using 1
  · congr 1
  · simp only [ENNReal.toNNReal_coe]

