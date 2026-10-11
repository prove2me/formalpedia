-- Prove2me | solution 1 for BookProof.WeylHamiltonian.selfAdjoint_sq_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:58.796925+00:00
-- url     : https://prove2.me/submissions/548415c1-391c-4bc4-9873-0af0484bb100

-- Generated from ChapterWeylHamiltonian.lean — solution of BookProof.WeylHamiltonian.selfAdjoint_sq_isPositive
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
open BookProof.WeylHamiltonian




open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : H →L[ℂ] H) (h : IsSelfAdjoint T) :
    (T ∘L T).IsPositive := by

  have hh : adjoint T = T := h
  have hp := isPositive_adjoint_comp_self T
  rwa [hh] at hp
