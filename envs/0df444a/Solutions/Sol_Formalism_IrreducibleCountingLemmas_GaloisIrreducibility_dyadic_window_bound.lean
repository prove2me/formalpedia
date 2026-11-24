-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dyadic_window_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:24.637864+00:00
-- url     : https://prove2.me/submissions/c82c6bed-82e6-45ad-b4f6-9b9bbf625e4d

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_half_pow_le_one
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
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
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : DyadicWindow := by
  intro P X κ hX hκ hP hcard
  by_contra hneg
  push_neg at hneg
  have hκX : 0 < κ * X := mul_pos hκ hX
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos (by norm_num : (0 : ℝ) < 2) hκ)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set W : ℕ → Finset ℕ := fun j =>
    P.filter (fun p : ℕ => X / 2 ^ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ j)) with hW
  set V := (Finset.Icc 1 M).filter (fun j => 2 * κ * X < X / 2 ^ j) with hV
  have hbig : P.filter (fun p : ℕ => 4 * κ * X < p) ⊆ V.biUnion W := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpP, hp4⟩ := hp
    have h1 : X / 2 ^ M < p := by
      have e : X / 2 ^ M = X * (1 / 2) ^ M := by rw [div_eq_mul_one_div, one_div_pow]
      rw [e]
      have : X * (1 / 2) ^ M < X * (2 * κ) := mul_lt_mul_of_pos_left hM hX
      linarith
    have hex : ∃ j : ℕ, X / 2 ^ j < p := ⟨M, h1⟩
    classical
    obtain ⟨j, hj, hjM, hjmin⟩ : ∃ j : ℕ, X / 2 ^ j < p ∧ j ≤ M ∧ ∀ m < j, ¬ (X / 2 ^ m < p) :=
      ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h1, fun m hm => Nat.find_min hex hm⟩
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero, div_one] at hj
        have := (hP p hpP).2
        linarith
      · exact h0
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hjprev : (p : ℝ) ≤ 2 * (X / 2 ^ j) := by
      have h2 := hjmin k (by omega)
      push_neg at h2
      have e : X / 2 ^ k = 2 * (X / 2 ^ j) := by
        rw [hk, pow_succ]
        ring
      linarith
    refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
    · rw [hV, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hj1, hjM⟩, ?_⟩
      linarith
    · rw [hW]
      simp only [Finset.mem_filter]
      exact ⟨hpP, hj.le, hjprev⟩
  have hbigc : ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) ≤ κ * X := by
    have h1 : (P.filter (fun p : ℕ => 4 * κ * X < p)).card ≤ ∑ j ∈ V, (W j).card :=
      (Finset.card_le_card hbig).trans Finset.card_biUnion_le
    have h2 : ∀ j ∈ V, ((W j).card : ℝ) ≤ κ * (X / 2 ^ j) := by
      intro j hj
      rw [hV, Finset.mem_filter, Finset.mem_Icc] at hj
      exact (hneg j hj.1.1 hj.2).le
    calc ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) ≤ ∑ j ∈ V, ((W j).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ j ∈ V, κ * (X / 2 ^ j) := Finset.sum_le_sum h2
      _ ≤ ∑ j ∈ Finset.Icc 1 M, κ * (X / 2 ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => (mul_pos hκ (div_pos hX (by positivity))).le)
      _ = κ * X * ∑ j ∈ Finset.Icc 1 M, (1 / (2 : ℝ) ^ j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ κ * X * 1 := mul_le_mul_of_nonneg_left (sum_half_pow_le_one M) hκX.le
      _ = κ * X := mul_one _
  have hsmall : ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ) ≤ 4 * κ * X := by
    have hsub : P.filter (fun p : ℕ => ¬ (4 * κ * X < p)) ⊆ Finset.Icc 1 ⌊4 * κ * X⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_Icc]
      refine ⟨(hP p hp.1).1, Nat.le_floor ?_⟩
      have h := hp.2
      push_neg at h
      exact h
    calc ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊4 * κ * X⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (⌊4 * κ * X⌋₊ : ℝ) := by simp
      _ ≤ 4 * κ * X := Nat.floor_le (by nlinarith)
  have htot : ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) +
      ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ) = P.card := by
    have h := Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => 4 * κ * X < p) (fun _ => (1 : ℝ))
    simpa using h
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
