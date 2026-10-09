-- Prove2me | solution 1 for BookProof.ChapterF2.deformedHamiltonian_monomial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:57:38.962725+00:00
-- url     : https://prove2.me/submissions/88b01b78-ac4a-4250-bed9-3d52c50bfdbd

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.deformedHamiltonian_monomial
import Mathlib
import Definitions.Def_ChapterF2
import Theorems.Thm_BookProof_ChapterF1_numberOp_monomial
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (n : ℕ) :
    deformedHamiltonian c (X ^ n) = (c * n) • X ^ n := by

  simp only [deformedHamiltonian, LinearMap.smul_apply, numberOp_monomial, smul_smul]
