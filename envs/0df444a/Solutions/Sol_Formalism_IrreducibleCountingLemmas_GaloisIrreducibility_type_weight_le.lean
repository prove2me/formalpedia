-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:28.980808+00:00
-- url     : https://prove2.me/submissions/70dc0671-dc2c-4a05-93ec-327b003b88ca

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_type_weight_upper_unit
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_irreducible_count_upper_unit
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_type_weight_exact
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_mul_count_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_multiset_eq_of_count
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_nonneg
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_cycle_type_probability
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
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (K : Type) [Field K] [Fintype K] (N : ℕ) (m : Multiset ℕ)
    (hm1 : ∀ d ∈ m, 1 ≤ d) (hm : m.sum = N) :
    ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m), sqWeight (monicOf c) ≤
      (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => σ.partition.parts = m)).card : ℝ) / (N.factorial : ℝ) := by
  classical
  set n : ℕ → ℕ := fun d => m.count d with hn
  have hsum : ∑ d ∈ Finset.Icc 1 N, d * n d = N := sum_mul_count_eq m N hm1 hm
  obtain ⟨S, hS, hSsum⟩ : ∃ S : Finset (Fin N → K),
      (∀ c ∈ sqSet K N, (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) → c ∈ S) ∧
      ∑ c ∈ S, sqWeight (monicOf c) = _ :=
    ⟨_, fun c hc h => by simp only [Finset.mem_filter]; exact ⟨hc, h⟩,
      type_weight_exact K N n hsum⟩
  obtain ⟨S', hS', hc⟩ : ∃ S' : Finset (Equiv.Perm (Fin N)),
      (∀ σ ∈ S', ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d) ∧
      S'.card * ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial :=
    ⟨_, fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ; exact hσ,
      cycle_type_probability N n hsum⟩
  have step1 : ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m),
      sqWeight (monicOf c) ≤ ∑ c ∈ S, sqWeight (monicOf c) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro c hc
      have hc' := Finset.mem_filter.mp hc
      exact hS c hc'.1 (fun d _ => by rw [hc'.2])
    · intro c _ _
      exact sqWeight_nonneg _
  have step2 := type_weight_upper_unit (Fintype.card K) (Finset.Icc 1 N)
    (fun d => ((Finset.univ : Finset (Fin d → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card) n
    Fintype.one_lt_card (fun d hd => (Finset.mem_Icc.mp hd).1)
    (fun d hd => irreducible_count_upper_unit K d (Finset.mem_Icc.mp hd).1)
  have hZpos : (0 : ℝ) < ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) := by
    apply Finset.prod_pos
    intro d hd
    have : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    positivity
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have hc' : (S'.card : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) =
      (N.factorial : ℝ) := by exact_mod_cast hc
  have step3 : 1 / ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) =
      (S'.card : ℝ) / (N.factorial : ℝ) := by
    rw [div_eq_div_iff hZpos.ne' hfac.ne', one_mul, hc']
  have step4 : S'.card ≤ ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => σ.partition.parts = m)).card := by
    apply Finset.card_le_card
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply multiset_eq_of_count _ _ N (fun d hd => σ.partition.parts_pos hd)
      (by rw [σ.partition.parts_sum, Fintype.card_fin]) hm1 hm
    intro d hd
    rw [Equiv.Perm.parts_partition, Multiset.count_add, hS' σ hσ d hd,
      Multiset.count_replicate, if_neg (by have := (Finset.mem_Icc.mp hd).1; omega), add_zero]
  calc _ ≤ ∑ c ∈ S, sqWeight (monicOf c) := step1
    _ = _ := hSsum
    _ ≤ _ := step2
    _ = (S'.card : ℝ) / (N.factorial : ℝ) := step3
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hfac.le
      exact_mod_cast step4
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
