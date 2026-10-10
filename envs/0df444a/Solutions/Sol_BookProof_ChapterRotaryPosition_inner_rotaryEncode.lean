-- Prove2me | solution 1 for BookProof.ChapterRotaryPosition.inner_rotaryEncode
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:11:32.559056+00:00
-- url     : https://prove2.me/submissions/f16f0dc5-62d8-4430-9fc1-631a5d34e6a7

-- Generated from ChapterRotaryPosition.lean — solution of BookProof.ChapterRotaryPosition.inner_rotaryEncode
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

variable {n m : ℕ}


private theorem rotaryEncode_apply (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (i : Fin n) :
    rotaryEncode omega p q i = Complex.exp ((p * omega i : ℝ) * Complex.I) * q i := rfl

set_option maxHeartbeats 1000000 in
theorem solution (omega : Fin n → ℝ) (a b : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (rotaryEncode omega a q) (rotaryEncode omega b k) : ℂ)
      = inner ℂ q (rotaryEncode omega (b - a) k) := by

  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconj : (starRingEnd ℂ) (Complex.exp ((a * omega i : ℝ) * Complex.I))
      = Complex.exp (-((a * omega i : ℝ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hexp : Complex.exp (-((a * omega i : ℝ) * Complex.I))
      * Complex.exp ((b * omega i : ℝ) * Complex.I)
      = Complex.exp (((b - a) * omega i : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [RCLike.inner_apply, rotaryEncode_apply, map_mul, hconj]
  linear_combination ((starRingEnd ℂ) (q i) * k i) * hexp
