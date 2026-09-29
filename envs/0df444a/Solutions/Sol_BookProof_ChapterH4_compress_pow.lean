-- Prove2me | solution 1 for BookProof.ChapterH4.compress_pow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:24:56.039784+00:00
-- url     : https://prove2.me/submissions/c640a4d0-d109-4d01-855a-543d92aa8883

-- Generated from ChapterH4.lean — solution of BookProof.ChapterH4.compress_pow
import Mathlib
import Definitions.Def_ChapterH4
import Theorems.Thm_BookProof_ChapterH4_compress_X_comp_V
open BookProof.ChapterH4










open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (n : ℕ) :
    (X ^ n).comp V = V.comp ((compress V X) ^ n) := by

  induction n with
  | zero => ?_
  | succ n ih => ?_
  · aesop;
  · convert congr_arg ( fun f => X.comp f ) ih using 1;
    · simp only [pow_succ']
      exact ContinuousLinearMap.ext (congrFun rfl)
    · simp only [pow_succ', ← ContinuousLinearMap.comp_assoc, compress_X_comp_V _ _ hVV hinv];
      exact ContinuousLinearMap.ext (congrFun rfl)
