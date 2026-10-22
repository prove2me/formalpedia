-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.cubic_no_relative_form_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:12:22.026519+00:00
-- url     : https://prove2.me/submissions/b9e06a65-be0e-4f23-ac46-fa875da7f6e0

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.cubic_no_relative_form_bound
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_vacuum_orthogonal
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_norm_sq
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_numberQuad
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_cubic_form
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (a b : ℝ) :
    ∃ u : FockAlg, u 0 = 0 ∧
      a * numberQuad u + b * ‖toLp u‖ ^ 2
        < (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re := by

  obtain ⟨n, hn⟩ := exists_nat_gt (((3 * |a| + 2 * |b|) / 2) ^ 2 + 1)
  have hnpos : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    have : (0 : ℝ) ≤ ((3 * |a| + 2 * |b|) / 2) ^ 2 := sq_nonneg _
    simp at hn
    linarith
  refine ⟨trial k n 1, trial_vacuum_orthogonal (by omega) 1, ?_⟩
  rw [trial_numberQuad, trial_norm_sq, trial_cubic_form k n hnpos 1]
  set s := Real.sqrt ((n : ℝ) + 1) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlow : ((n : ℝ) + 1) * s
      ≤ Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    rw [Real.le_sqrt (by positivity)]
    · nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · positivity
  have hK : a * ((n : ℝ) + ((n : ℝ) + 3) * 1 ^ 2) + b * (1 + 1 ^ 2)
      ≤ (3 * |a| + 2 * |b|) * ((n : ℝ) + 1) := by
    nlinarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b,
      Nat.cast_nonneg (α := ℝ) n]
  have hbig : (3 * |a| + 2 * |b|) / 2 < s := by
    have hsq : ((3 * |a| + 2 * |b|) / 2) ^ 2 < s ^ 2 := by
      rw [hs2]; linarith
    nlinarith [abs_nonneg a, abs_nonneg b]
  nlinarith [mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 2)]
