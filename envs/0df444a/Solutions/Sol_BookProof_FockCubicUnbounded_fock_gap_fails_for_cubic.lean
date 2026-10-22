-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.fock_gap_fails_for_cubic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:12:34.552012+00:00
-- url     : https://prove2.me/submissions/a0a5fa2a-57d5-417c-b77c-d8ad2a7816bc

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.fock_gap_fails_for_cubic
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_vacuum_orthogonal
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_norm_sq
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_numberQuad
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_cubic_form
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) {lam : ℝ} (hlam : 0 < lam) (M : ℝ) :
    ∃ u : FockAlg, u 0 = 0 ∧
      (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re
          + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
        ≤ -M * ‖toLp u‖ ^ 2 := by

  obtain ⟨n, hn⟩ := exists_nat_gt (((3 + 2 * |M|) / (2 * lam)) ^ 2 + 1)
  have hnpos : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    have : (0 : ℝ) ≤ ((3 + 2 * |M|) / (2 * lam)) ^ 2 := sq_nonneg _
    simp at hn
    linarith
  refine ⟨trial k n (-1), trial_vacuum_orthogonal (by omega) (-1), ?_⟩
  have hnum : (inner ℂ (toLp (trial k n (-1)))
      (toLp (dGamma numberCol (trial k n (-1)))) : ℂ).re = numberQuad (trial k n (-1)) := rfl
  rw [hnum, trial_numberQuad, trial_norm_sq, trial_cubic_form k n hnpos (-1)]
  set s := Real.sqrt ((n : ℝ) + 1) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlow : ((n : ℝ) + 1) * s
      ≤ Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    rw [Real.le_sqrt (by positivity)]
    · nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · positivity
  have hM : (n : ℝ) + ((n : ℝ) + 3) * (-1 : ℝ) ^ 2 + M * (1 + (-1 : ℝ) ^ 2)
      ≤ (3 + 2 * |M|) * ((n : ℝ) + 1) := by
    nlinarith [le_abs_self M, abs_nonneg M, Nat.cast_nonneg (α := ℝ) n]
  have hbig : (3 + 2 * |M|) / (2 * lam) < s := by
    have hsq : ((3 + 2 * |M|) / (2 * lam)) ^ 2 < s ^ 2 := by
      rw [hs2]; linarith
    have hnn : 0 ≤ (3 + 2 * |M|) / (2 * lam) := by positivity
    nlinarith
  have hbig' : 3 + 2 * |M| < 2 * lam * s := by
    rw [div_lt_iff₀ (by positivity)] at hbig
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlow (le_of_lt hlam),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hs0]
