-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.irreducible_count_upper_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:12.860909+00:00
-- url     : https://prove2.me/submissions/05bbf0e7-e8b7-496b-b8c0-6c2f46b22458

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
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_injective
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
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
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : IrredCountUpperUnit := by
  classical
  intro K _ _ d hd
  set F := (Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hF
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < (Nat.card K) ^ d - 1 := by
    have : 1 < (Nat.card K) ^ d := Nat.one_lt_pow (by omega) hq
    omega
  have hdvd : ∏ c ∈ F, monicOf c ∣ (X ^ (Nat.card K) ^ d - X : K[X]) := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      have hia : Irreducible (monicOf a) := (Finset.mem_filter.mp ha).2.1
      have hib : Irreducible (monicOf b) := (Finset.mem_filter.mp hb).2.1
      rw [Function.onFun, hia.coprime_iff_not_dvd]
      intro h
      exact hab (monicOf_injective (eq_of_monic_of_associated (monicOf_monic a) (monicOf_monic b)
        (hia.associated_of_dvd hib h)))
    · intro c hc
      exact ((Finset.mem_filter.mp hc).2.1.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp
        (by rw [monicOf_natDegree])
  have hsplit : (X ^ (Nat.card K) ^ d - X : K[X]) = X * (X ^ ((Nat.card K) ^ d - 1) - C 1) := by
    rw [mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega), C_1, mul_one]
  have hcop : IsCoprime (∏ c ∈ F, monicOf c) (X : K[X]) := by
    apply IsCoprime.prod_left
    intro c hc
    have hic : Irreducible (monicOf c) := (Finset.mem_filter.mp hc).2.1
    rw [hic.coprime_iff_not_dvd]
    intro h
    have h1 : (X : K[X]) ∣ monicOf c := (hic.associated_of_dvd irreducible_X h).symm.dvd
    exact (Finset.mem_filter.mp hc).2.2 (X_dvd_iff.mp h1)
  rw [hsplit] at hdvd
  have hdvd2 := hcop.dvd_of_dvd_mul_left hdvd
  have hdeg := natDegree_le_of_dvd hdvd2 (X_pow_sub_C_ne_zero hpos 1)
  rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c), natDegree_X_pow_sub_C] at hdeg
  simp only [monicOf_natDegree, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card] at hdeg
  rw [mul_comm]
  exact hdeg
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
