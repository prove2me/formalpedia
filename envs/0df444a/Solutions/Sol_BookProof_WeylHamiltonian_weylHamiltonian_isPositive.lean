-- Prove2me | solution 1 for BookProof.WeylHamiltonian.weylHamiltonian_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:45:54.459807+00:00
-- url     : https://prove2.me/submissions/998fe3e0-0ee3-4c3b-bed1-52b2dca228db

-- Generated from ChapterWeylHamiltonian.lean — solution of BookProof.WeylHamiltonian.weylHamiltonian_isPositive
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
import Theorems.Thm_BookProof_WeylHamiltonian_selfAdjoint_sq_isPositive
import Theorems.Thm_BookProof_WeylHamiltonian_smul_nonneg_isPositive
open BookProof.WeylHamiltonian




open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in

theorem solution {n m : ℕ}
    (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H)
    (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a)) :
    (weylHamiltonian π B).IsPositive := by
  refine ContinuousLinearMap.IsPositive.add ?_ ?_
  · refine smul_nonneg_isPositive _ ?_ (by norm_num)
    exact ContinuousLinearMap.isPositive_sum _ (fun i _ => selfAdjoint_sq_isPositive _ (hπ i))
  · refine smul_nonneg_isPositive _ ?_ (by norm_num)
    exact ContinuousLinearMap.isPositive_sum _ (fun a _ => selfAdjoint_sq_isPositive _ (hB a))
