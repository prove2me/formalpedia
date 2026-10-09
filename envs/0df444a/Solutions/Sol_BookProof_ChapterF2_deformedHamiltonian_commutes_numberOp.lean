-- Prove2me | solution 1 for BookProof.ChapterF2.deformedHamiltonian_commutes_numberOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:58:02.963855+00:00
-- url     : https://prove2.me/submissions/d042df75-0ff3-410a-9a6d-db712ba06950

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.deformedHamiltonian_commutes_numberOp
import Mathlib
import Definitions.Def_ChapterF2
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) :
    deformedHamiltonian c ∘ₗ numberOp = numberOp ∘ₗ deformedHamiltonian c := by

  ext p; simp [deformedHamiltonian, LinearMap.smul_apply]
