-- Prove2me | solution 1 for DarbouxRS.upperLowerCommonLimit_const_mul_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:12:23.510593+00:00
-- url     : https://prove2.me/submissions/ba119584-2129-46a3-9321-7e3a52437b28

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F003
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_sourceHypotheses_const_mul_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

/-- Scaling preserves both Darboux error bounds, including negative scalars. -/
private theorem source_upper_lower_scale_error
    {a b c eps L : ℝ} {f alpha : ℝ → ℝ}
    (P : Partition a b) (heps : 0 < eps)
    (hP : |upperSum P f alpha - L| < eps / (|c| + 1) ∧
          |lowerSum P f alpha - L| < eps / (|c| + 1)) :
    |upperSum P (fun x => c * f x) alpha - c * L| < eps ∧
    |lowerSum P (fun x => c * f x) alpha - c * L| < eps := by
  let C : ℝ := |c| + 1
  by_cases hc : 0 ≤ c
  · constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [upperSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [upperSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)

theorem solution {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  exact source_upper_lower_scale_error P heps (by simpa [C] using H P hmesh)
