-- Prove2me | solution 1 for BookProof.ChapterF2.bargmann_numberOp_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:57:25.113203+00:00
-- url     : https://prove2.me/submissions/ef4e5286-ff6b-4af5-851a-f24fd88bf55d

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.bargmann_numberOp_re
import Mathlib
import Definitions.Def_ChapterF2
import Theorems.Thm_BookProof_ChapterF2_numberOp_coeff
import Theorems.Thm_BookProof_ChapterF2_numberOp_support
import Theorems.Thm_BookProof_ChapterF1_bargmann_eq_sum
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p : ℂ[X]) :
    (bargmann p (numberOp p)).re
      = ∑ n ∈ p.support, ((n : ℝ) * n.factorial) * Complex.normSq (p.coeff n) := by

  rw [bargmann_eq_sum p (numberOp p) (Finset.Subset.refl _) (numberOp_support p), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [numberOp_coeff]
  have : (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n) * ((n : ℂ) * p.coeff n)
      = ((n : ℂ) * n.factorial) * (p.coeff n * (starRingEnd ℂ) (p.coeff n)) := by ring
  rw [this, Complex.mul_conj]; simp
