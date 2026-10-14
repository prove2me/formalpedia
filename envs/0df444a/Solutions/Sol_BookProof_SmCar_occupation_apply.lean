-- Prove2me | solution 1 for BookProof.SmCar.occupation_apply
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:40:54.767559+00:00
-- url     : https://prove2.me/submissions/8f0739c4-8967-42ee-9320-7027f8845e34

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.occupation_apply
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}
open BookProof.SmCar

theorem solution(i : Fin n) (ψ : FermiFock n) (S : Finset (Fin n)) :
    (creat i (annih i ψ)) S = if i ∈ S then ψ S else 0 := by
  by_cases h : i ∈ S <;> simp [BookProof.SmCar.creat, BookProof.SmCar.annih, h, Finset.insert_erase, jwSign, ← mul_assoc, ← mul_pow]
