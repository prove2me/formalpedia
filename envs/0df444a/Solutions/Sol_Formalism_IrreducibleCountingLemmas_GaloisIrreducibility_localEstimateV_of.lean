-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.localEstimateV_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:36.801323+00:00
-- url     : https://prove2.me/submissions/82e9088f-3ce3-43b9-9787-7826a582cfe0

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic__60d833550372
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial Formalism.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (h : TypeSetWeight) (hC : CycleProbSum) (hS : PrimeRecipSum) :
    LocalEstimateV := by
  intro K _ _ N hN
  classical
  have hiff : ∀ f : K[X], f ≠ 0 → ((∃ P : K[X], Irreducible P ∧ P ∣ f ∧ P.natDegree.Prime ∧
      N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) ↔
      ∃ p ∈ degType f, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro f hf
    constructor
    · rintro ⟨P, hPi, hPd, hp⟩
      obtain ⟨q, hq, hPq⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf hPi hPd
      have hdeg : P.natDegree = q.natDegree :=
        Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hPq)
      refine ⟨q.natDegree, Multiset.mem_map.2 ⟨q, hq, rfl⟩, ?_⟩
      rw [← hdeg]
      exact hp
    · rintro ⟨p, hp, hpp⟩
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨q, UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq, hpp⟩
  have hfilt : (sqSet K N).filter (fun c => ¬ ∃ P : K[X], Irreducible P ∧ P ∣ monicOf c ∧
      P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) =
      (sqSet K N).filter (fun c => ¬ ∃ p ∈ degType (monicOf c), p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    apply Finset.filter_congr
    intro c _
    rw [hiff _ (monicOf_monic' c).ne_zero]
  rw [hfilt]
  have hT := h K N (fun m => ¬ ∃ p ∈ m, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)
  have hparts : ∀ σ : Equiv.Perm (Fin N), (∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) ↔
      (∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro σ
    rw [Equiv.Perm.parts_partition]
    constructor
    · rintro ⟨p, hp, hpp⟩
      rcases Multiset.mem_add.1 hp with h1 | h1
      · exact ⟨p, h1, hpp⟩
      · rw [Multiset.eq_of_mem_replicate h1] at hpp
        exact absurd hpp.1 Nat.not_prime_one
    · rintro ⟨p, hp, hpp⟩
      exact ⟨p, Multiset.mem_add.2 (Or.inl hp), hpp⟩
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hgoal : (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ =>
      ¬ ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) / N.factorial ≤
      1 - 1 / (5 * Real.log N) := by
    rw [div_le_iff₀ hf]
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)
    simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hadd
    beta_reduce at hadd
    have hQ : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) =
        Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
          ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N :=
      Finset.filter_congr (fun σ _ => hparts σ)
    rw [hQ] at hadd
    have hadd' := congrArg (fun n : ℕ => (n : ℝ)) hadd
    simp only [Nat.cast_add] at hadd'
    rw [hC N] at hadd'
    have hsum := hS N hN
    have hsum' : ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N,
        (N.factorial : ℝ) / p =
        N.factorial * ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N,
          1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
    rw [hsum'] at hadd'
    nlinarith [mul_le_mul_of_nonneg_left hsum hf.le]
  exact le_trans (le_of_eq (by congr)) (le_trans hT (le_trans (le_of_eq (by congr)) hgoal))
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
