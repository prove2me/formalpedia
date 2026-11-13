-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB210_continuous_gradient_compact_clip_uniform_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:43:01.096442+00:00
-- url     : https://prove2.me/submissions/2554f8f4-a341-4e01-85d9-3862ba0fbcdc

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
noncomputable section

/-- Compactness bounds the clipped gradient uniformly on the whole real line. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hContinuous : ContinuousOn (deriv w) (Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
      |if y ∈ Icc a b then deriv w y else 1| ≤ B := by
  have hc : IsCompact ((deriv w) '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hContinuous
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  refine ⟨max B 1, le_trans (by norm_num) (le_max_right B 1), ?_⟩
  intro y
  by_cases hy : y ∈ Icc a b
  · simp only [if_pos hy]
    calc
      |deriv w y| = ‖deriv w y‖ := (Real.norm_eq_abs _).symm
      _ ≤ B := hB _ (mem_image_of_mem _ hy)
      _ ≤ max B 1 := le_max_left B 1
  · simpa only [if_neg hy, abs_one] using le_max_right B 1

