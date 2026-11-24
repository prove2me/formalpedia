-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.excluded_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:30.010682+00:00
-- url     : https://prove2.me/submissions/5009b1fb-ddaf-4309-bee8-e9138fbdde7d

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRExcludedCount
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_pow_class_le
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bad_primes_cardinality
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bad_primes_divides
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
theorem _root_.solution : ExcludedCount := by
  classical
  intro N g₁ Y S hN hY hg₁ hS
  set c : ℝ := Y ^ ((3 : ℝ) / 4) + 1 with hc
  have hc0 : (0 : ℝ) ≤ c := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  have hcover : S ⊆ (BB g₁ N).biUnion (fun l => S.filter (fun g => l ∈ BB g N)) := by
    intro g hg
    obtain ⟨_, _, _, hnd⟩ := hS g hg
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨l, h1, h2⟩ := hnd
    exact Finset.mem_biUnion.mpr ⟨l, h1, Finset.mem_filter.mpr ⟨hg, h2⟩⟩
  have hper : ∀ l ∈ BB g₁ N,
      ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by
    intro l hlB
    have hl : l.Prime := by
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlB
      rcases hlB with rfl | ⟨_, h2, _⟩
      · exact hg₁
      · exact h2
    have hex : ∃ j : ℕ, Y < (l : ℝ) ^ (4 * j) := by
      have h1 : (1 : ℝ) < (l : ℝ) ^ 4 := by
        have : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
        exact one_lt_pow₀ this (by norm_num)
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Y h1
      exact ⟨n, by rw [pow_mul]; exact hn⟩
    set j := Nat.find hex with hjdef
    have hj : Y < (l : ℝ) ^ (4 * j) := Nat.find_spec hex
    have hmin : ∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y := fun i hi => not_lt.mp (Nat.find_min hex hi)
    set F : ℕ → Finset ℕ := fun d => S.filter (fun g => l ^ j ∣ g ^ d - 1) with hF
    have hsub : S.filter (fun g => l ∈ BB g N) ⊆ insert l ((Finset.Icc 1 N).biUnion F) := by
      intro g hg
      obtain ⟨hgS, hlg⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgp, hYg, _, _⟩ := hS g hgS
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlg
      rcases hlg with rfl | ⟨_, _, d, hd, h3⟩
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩)
        rw [hF]
        refine Finset.mem_filter.mpr ⟨hgS, ?_⟩
        exact bad_primes_divides l g d j Y hl (Finset.mem_Icc.mp hd).1 hgp.two_le hYg h3 hj hmin
    have hFd : ∀ d ∈ Finset.Icc 1 N, ((F d).card : ℝ) ≤ 2 * N * c := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have h1 := card_pow_class_le (F d) Y l j d hl hd1 hY hj (by
        intro g hg
        obtain ⟨hgS, hdv⟩ := Finset.mem_filter.mp hg
        exact ⟨(hS g hgS).2.1, (hS g hgS).2.2.1, hdv⟩)
      have hdN' : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      calc ((F d).card : ℝ) ≤ 2 * d * c := h1
        _ ≤ 2 * N * c := by
            apply mul_le_mul_of_nonneg_right _ hc0
            linarith
    have h1 : (S.filter (fun g => l ∈ BB g N)).card ≤
        (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
      calc (S.filter (fun g => l ∈ BB g N)).card
          ≤ (insert l ((Finset.Icc 1 N).biUnion F)).card := Finset.card_le_card hsub
        _ ≤ ((Finset.Icc 1 N).biUnion F).card + 1 := Finset.card_insert_le _ _
        _ ≤ (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
            Nat.add_le_add_right Finset.card_biUnion_le 1
    have h2 : ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤
        (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) + 1 := by exact_mod_cast h1
    have h3 : (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) ≤ ∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c :=
      Finset.sum_le_sum hFd
    have h4 : (∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c) = 2 * (N : ℝ) ^ 2 * c := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel]
      ring
    linarith
  have hB0 : (0 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by positivity
  have hBB : ((BB g₁ N).card : ℝ) ≤ 3 * N + 1 := by
    exact_mod_cast bad_primes_cardinality g₁ N hg₁.two_le
  have h1 : S.card ≤ ∑ l ∈ BB g₁ N, (S.filter (fun g => l ∈ BB g N)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := by
    exact_mod_cast h1
  calc (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := h2
    _ ≤ ∑ _l ∈ BB g₁ N, (1 + 2 * (N : ℝ) ^ 2 * c) := Finset.sum_le_sum hper
    _ = ((BB g₁ N).card : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := mul_le_mul_of_nonneg_right hBB hB0
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
