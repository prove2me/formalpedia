-- Prove2me | solution 1 for BookProof.ChapterF2.numberOp_support
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:57:11.121725+00:00
-- url     : https://prove2.me/submissions/db7df663-9134-47a0-a480-302d3eff628e

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.numberOp_support
import Mathlib
import Definitions.Def_ChapterF2
import Theorems.Thm_BookProof_ChapterF2_numberOp_coeff
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p : ℂ[X]) : (numberOp p).support ⊆ p.support := by

  intro n hn
  simp only [Polynomial.mem_support_iff] at *
  intro h; apply hn; rw [numberOp_coeff, h, mul_zero]
