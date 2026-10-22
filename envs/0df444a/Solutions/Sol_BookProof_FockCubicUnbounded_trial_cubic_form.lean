-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_cubic_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:54:01.92734+00:00
-- url     : https://prove2.me/submissions/56ca1396-cf8f-4cd2-9651-7332e3153889

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.trial_cubic_form
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_confAt_self
import Theorems.Thm_BookProof_FockCubicUnbounded_confAt_injective
import Theorems.Thm_BookProof_FockCubicUnbounded_up_confAt
import Theorems.Thm_BookProof_FockCubicUnbounded_dn_confAt
import Theorems.Thm_BookProof_FockCubicUnbounded_cubeA_coord
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_support_subset
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n3
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_other
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
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
theorem solution (k n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re
      = 2 * c * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by

  classical
  have hne : confAt k n ≠ confAt k (n + 3) := by
    intro h
    have := confAt_injective k h
    omega
  have hsqrt : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))
      = Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 3) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hval_n : cubeA k (trial k n c) (confAt k n)
      = ((c : ℝ) : ℂ)
          * ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) : ℝ) : ℂ) := by
    rw [cubeA_coord]
    simp only [dn_confAt, up_confAt, confAt_self]
    rw [trial_at_other (k := k) (c := c) (m := n - 1 - 1 - 1) (by omega) (by omega),
      show n + 1 + 1 + 1 = n + 3 from by omega, trial_at_n3, hsqrt]
    push_cast
    ring_nf
  have hval_n3 : cubeA k (trial k n c) (confAt k (n + 3))
      = ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) : ℝ) : ℂ) := by
    have e1 : n + 3 - 1 = n + 2 := by omega
    have e2 : n + 2 - 1 = n + 1 := by omega
    have e3 : n + 1 - 1 = n := by omega
    rw [cubeA_coord]
    simp only [dn_confAt, up_confAt, confAt_self, e1, e2, e3]
    rw [trial_at_n, trial_at_other (k := k) (c := c) (by omega) (by omega), hsqrt]
    push_cast
    ring
  have hinner := inner_toLp_of_subset (trial_support_subset k n c) (cubeA k (trial k n c))
  have hsum : (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ)
      = ((2 * c * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) : ℝ) : ℂ) := by
    rw [hinner, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
      hval_n, hval_n3, trial_at_n, trial_at_n3]
    push_cast
    simp [Complex.conj_ofReal]
    ring
  have := congrArg Complex.re hsum
  simpa using this
