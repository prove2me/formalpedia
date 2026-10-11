-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.normSq_exp_mul_I
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:39.348771+00:00
-- url     : https://prove2.me/submissions/a740f8c5-68ef-4713-a375-0a65fd691ce7

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.normSq_exp_mul_I
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℝ) :
    Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by

  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.normSq_add_mul_I]
  exact Real.cos_sq_add_sin_sq θ
