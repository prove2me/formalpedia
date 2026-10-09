-- Prove2me | solution 1 for BookProof.ChapterF2.bargmann_self_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:57:24.037996+00:00
-- url     : https://prove2.me/submissions/b0d60adf-274d-4c3d-b3d1-0d338eeb2e92

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.bargmann_self_re
import Mathlib
import Definitions.Def_ChapterF2
import Theorems.Thm_BookProof_ChapterF1_bargmann_eq_sum
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p : ℂ[X]) :
    (bargmann p p).re = ∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n) := by

  rw [bargmann_eq_sum p p (Finset.Subset.refl _) (Finset.Subset.refl _), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have : (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n) * p.coeff n
      = (n.factorial : ℂ) * (p.coeff n * (starRingEnd ℂ) (p.coeff n)) := by ring
  rw [this, Complex.mul_conj]; simp
