-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:55.190017+00:00
-- url     : https://prove2.me/submissions/7df2f387-d808-4d6d-8e9b-c1c04837977c

-- Generated from ChapterSinusoidalPosition.lean — solution of BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSinusoidalPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin n → ℝ) (p q : ℝ) :
    peInner w p q = ∑ a, Real.cos (w a * (p - q)) := by

  refine Finset.sum_congr rfl fun a _ => ?_
  have h : w a * (p - q) = w a * p - w a * q := by ring
  rw [h, Real.cos_sub]
  simp only [sinusoidalEncode]
  ring
