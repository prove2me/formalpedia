-- Prove2me | solution 1 for BookProof.ChapterF2.hamiltonian_commutes_numberOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:58:27.316795+00:00
-- url     : https://prove2.me/submissions/1a732abe-55f9-4dd9-8f1c-59ac59753a0e

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.hamiltonian_commutes_numberOp
import Mathlib
import Definitions.Def_ChapterF2
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    hamiltonian ∘ₗ numberOp = numberOp ∘ₗ hamiltonian := rfl
