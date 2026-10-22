-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_numberQuad
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:53:50.258547+00:00
-- url     : https://prove2.me/submissions/39f7cea8-499c-4e0d-a310-512d5d2386e8

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.trial_numberQuad
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_confAt_injective
import Theorems.Thm_BookProof_FockCubicUnbounded_confNumber_confAt
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_support_subset
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n3
import Theorems.Thm_BookProof_FockOneParticleGap_confEnergy_one
import Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_apply
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
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
theorem solution (k n : ℕ) (c : ℝ) :
    numberQuad (trial k n c) = (n : ℝ) + ((n : ℝ) + 3) * c ^ 2 := by

  classical
  have hne : confAt k n ≠ confAt k (n + 3) := by
    intro h
    have := confAt_injective k h
    omega
  have hcoord : ∀ γ : Conf, dGamma numberCol (trial k n c) γ
      = ((confNumber γ : ℝ) : ℂ) * trial k n c γ := by
    intro γ
    rw [numberCol, dGamma_diagCol_apply, confEnergy_one]
  have hinner := inner_toLp_of_subset (trial_support_subset k n c)
    (dGamma numberCol (trial k n c))
  have hsum : (inner ℂ (toLp (trial k n c)) (toLp (dGamma numberCol (trial k n c))) : ℂ)
      = (((n : ℝ) + ((n : ℝ) + 3) * c ^ 2 : ℝ) : ℂ) := by
    rw [hinner, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
      hcoord, hcoord, trial_at_n, trial_at_n3, confNumber_confAt, confNumber_confAt]
    push_cast
    simp [Complex.conj_ofReal]
    ring
  have := congrArg Complex.re hsum
  simpa [numberQuad, ← Complex.ofReal_pow] using this
