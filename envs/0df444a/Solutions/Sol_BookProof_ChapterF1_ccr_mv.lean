-- Prove2me | solution 1 for BookProof.ChapterF1.ccr_mv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:54:58.525852+00:00
-- url     : https://prove2.me/submissions/a8f93fce-7686-4271-b00b-75717db88a6f

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.ccr_mv
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) :
    (MvPolynomial.pderiv i) (MvPolynomial.X j * p)
      - MvPolynomial.X j * (MvPolynomial.pderiv i) p
      = (if i = j then p else 0) := by

  split_ifs <;> simp_all [ MvPolynomial.pderiv_X ]
