-- Prove2me | solution 1 for BookProof.ChapterEulerComplexQuat.quat_reproduces
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:43:06.843973+00:00
-- url     : https://prove2.me/submissions/5b45312e-97cf-47df-9d6b-cb67615fcb4b

-- Generated from ChapterEulerComplexQuat.lean — solution of BookProof.ChapterEulerComplexQuat.quat_reproduces
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat



open scoped Quaternion BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) :
    ∃ v : Fin n → ℍ[ℝ], (∑ k, Quaternion.normSq (v k) = 1) ∧ ∀ k, qbornProb v k = p k := by

  refine ⟨fun k => ((Real.sqrt (p k) : ℝ) : ℍ[ℝ]), ?_, ?_⟩
  · rw [← hp1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : Quaternion.normSq ((Real.sqrt (p k) : ℝ) : ℍ[ℝ]) = Real.sqrt (p k) ^ 2 := by
      simp [Quaternion.normSq_def']
    rw [this, Real.sq_sqrt (hp0 k)]
  · intro k
    have : Quaternion.normSq ((Real.sqrt (p k) : ℝ) : ℍ[ℝ]) = Real.sqrt (p k) ^ 2 := by
      simp [Quaternion.normSq_def']
    rw [qbornProb, this, Real.sq_sqrt (hp0 k)]
