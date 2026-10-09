-- Prove2me | solution 1 for BookProof.ChapterF1.bargmann_monomial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:55:51.206518+00:00
-- url     : https://prove2.me/submissions/e2d52e2e-9264-4f21-b6bd-4115694620bc

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.bargmann_monomial
import Mathlib
import Definitions.Def_ChapterF1
import Theorems.Thm_BookProof_ChapterF1_bargmann_monomial_left
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m n : ℕ) :
    bargmann (X ^ m) (X ^ n) = if m = n then (n.factorial : ℂ) else 0 := by

  convert bargmann_monomial_left m ( X ^ n ) using 1 ; aesop
