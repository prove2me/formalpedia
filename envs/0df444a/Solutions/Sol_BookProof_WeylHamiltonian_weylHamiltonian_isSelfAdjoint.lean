-- Prove2me | solution 1 for BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:46:10.13699+00:00
-- url     : https://prove2.me/submissions/83f0dd6c-371e-4612-96e5-ae744f52edcc

-- Generated from ChapterWeylHamiltonian.lean — solution of BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
open BookProof.WeylHamiltonian




open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in

theorem solution {n m : ℕ}
    (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H)
    (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a)) :
    IsSelfAdjoint (weylHamiltonian π B) := by
  have h_sq_selfAdjoint : ∀ i, IsSelfAdjoint ((π i) ∘L (π i)) := by
    simp_all [IsSelfAdjoint]
    simp_all [star, ContinuousLinearMap.ext_iff]
  have h_B_sq_selfAdjoint : ∀ a, IsSelfAdjoint ((B a) ∘L (B a)) := by
    simp_all [IsSelfAdjoint, ContinuousLinearMap.ext_iff]
    simp_all [star, ContinuousLinearMap.comp_apply]
  unfold weylHamiltonian
  simp_all [IsSelfAdjoint, Finset.smul_sum]
