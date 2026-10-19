-- Prove2me | solution 1 for BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:20:45.224449+00:00
-- url     : https://prove2.me/submissions/c02e9c30-0f33-48fe-8900-e19580514ca6

import Mathlib
import Definitions.Def_ChapterReconstruct
-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}


theorem solution (U : Fin n → Fin n → ℂ) (a : Fin n)
    (hU : IsDeterministicCol U a) (Ψ : Fin n → ℂ) : offDiag U a Ψ = 0 := by
  unfold BookProof.ChapterReconstruct.offDiag
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro b _
  split_ifs with hkb
  · rfl
  · have h := hU b k (Ne.symm hkb)
    linear_combination (Ψ k * (starRingEnd ℂ) (Ψ b)) * h

