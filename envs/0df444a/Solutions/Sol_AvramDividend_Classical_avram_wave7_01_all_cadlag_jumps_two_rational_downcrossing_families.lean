-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:55:11.011238+00:00
-- url     : https://prove2.me/submissions/27f0136a-6076-4a4d-9027-2b352043d6d3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_local_strict_downjump_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_left_limit_negation_at_positive_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Any real càdlàg jump is a downcrossing of the path or its negation. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    ∀ u : ℝ≥0, 0 < u →
      Y u - Function.leftLim Y u ≠ 0 →
      (∃ k : ℕ,
        (⨅ n : ℕ,
          {Z : ℝ≥0 → ℝ |
            grid (pairs k).1 < grid n ∧
            Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
            (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal = u) ∨
      (∃ k : ℕ,
        (⨅ n : ℕ,
          {Z : ℝ≥0 → ℝ |
            grid (pairs k).1 < grid n ∧
            Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
            (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤)
            (fun v : ℝ≥0 => -Y v)).toNNReal = u) := by
  have hNegR (v : ℝ≥0) :
      ContinuousWithinAt (fun x : ℝ≥0 => -Y x) (Ici v) v :=
    (hRight v).neg
  have hNegL (v : ℝ≥0) (hv : 0 < v) :
      Tendsto (fun x : ℝ≥0 => -Y x) (𝓝[<] v)
        (𝓝 (Function.leftLim (fun x : ℝ≥0 => -Y x) v)) := by
    have hEq :=
      avram_wave7_01_left_limit_negation_at_positive_time
        Y v hv (hLeft v hv)
    rw [hEq]
    exact (hLeft v hv).neg
  intro u hu hj
  have hne : Y u ≠ Function.leftLim Y u := sub_ne_zero.mp hj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left
    exact avram_wave7_01_local_strict_downjump_rational_grid_coverage
      Y hRight hLeft grid hdense pairs hpairs u hu hlt
  · right
    have hEq :=
      avram_wave7_01_left_limit_negation_at_positive_time
        Y u hu (hLeft u hu)
    have hNegLt :
        -Y u < Function.leftLim (fun x : ℝ≥0 => -Y x) u := by
      rw [hEq]
      exact neg_lt_neg hgt
    exact avram_wave7_01_local_strict_downjump_rational_grid_coverage
      (fun x : ℝ≥0 => -Y x) hNegR hNegL
      grid hdense pairs hpairs u hu hNegLt
