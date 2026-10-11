-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:30:00.157085+00:00
-- url     : https://prove2.me/submissions/b45e00d4-08f4-4f44-93aa-e1c4c7731114

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta t₀ : ℝ) (c : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (beta * (c + t)))
      (beta * Real.exp (beta * (c + t₀))) t₀ := by

  have h : HasDerivAt (fun t : ℝ => beta * (c + t)) beta t₀ := by
    simpa using ((hasDerivAt_id t₀).const_add c).const_mul beta
  simpa [mul_comm] using h.exp
