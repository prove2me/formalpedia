-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_isFunctionOfSpectrum_iff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:39:50.813046+00:00
-- url     : https://prove2.me/submissions/a1a1fc46-3424-42b3-8315-1bfac823c540
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_isFunctionOfSpectrum_iff
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_permOp_basisVec
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_exists_eigenvalue_of_isFunctionOfSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (σ : Equiv.Perm X) :
    IsFunctionOfSpectrum (permOp σ) ↔ σ = 1 := by

  classical
  constructor
  · intro hσ
    ext y
    obtain ⟨c, hc⟩ := exists_eigenvalue_of_isFunctionOfSpectrum hσ y
    rw [permOp_basisVec] at hc
    have h := congrArg (fun f : X → ℂ => f (σ y)) hc
    simp only [basisVec, Pi.smul_apply, smul_eq_mul] at h
    by_cases hy : σ y = y
    · simpa using hy
    · rw [if_neg hy, mul_zero] at h
      exact absurd h one_ne_zero
  · rintro rfl
    refine ⟨fun _ => 1, ?_⟩
    ext f x
    show f ((1 : Equiv.Perm X).symm x) = 1 * f x
    simp [Equiv.Perm.one_def]
