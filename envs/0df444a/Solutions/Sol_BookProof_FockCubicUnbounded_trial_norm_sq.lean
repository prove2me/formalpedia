-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:53:49.090319+00:00
-- url     : https://prove2.me/submissions/fe88e3d8-a5c4-4278-aeaa-67c4a649f49f

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.trial_norm_sq
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_confAt_injective
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_support_subset
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n3
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
theorem solution (k n : ℕ) (c : ℝ) : ‖toLp (trial k n c)‖ ^ 2 = 1 + c ^ 2 := by

  classical
  have hne : confAt k n ≠ confAt k (n + 3) := by
    intro h
    have := confAt_injective k h
    omega
  have hinner := inner_toLp_of_subset (trial_support_subset k n c) (trial k n c)
  have hsum : (inner ℂ (toLp (trial k n c)) (toLp (trial k n c)) : ℂ)
      = ((1 + c ^ 2 : ℝ) : ℂ) := by
    rw [hinner, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
      trial_at_n, trial_at_n3]
    push_cast
    simp [Complex.conj_ofReal]
    ring
  have := congrArg Complex.re hsum
  rw [inner_self_eq_norm_sq_to_K] at this
  simpa [← Complex.ofReal_pow] using this
