-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityBounds.condProb_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:22.251051+00:00
-- url     : https://prove2.me/submissions/088f9bed-0236-48a8-b3db-fcba27b2f3b3

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityBounds
open Finset
namespace Formalism.G0.TopsConditionalProbabilityBounds
theorem _root_.solution (n : ℕ) (δ : ℝ) (S : Finset ℕ) (hS : S ⊆ range n) (h0 : 0 ∉ S)
    (hn : 1 ≤ n) :
    condProb n δ (fun T => Disjoint S T) = (1 - δ) ^ S.card := by
  classical
  set U := (range n \ S).erase 0 with hU
  have h0U : 0 ∈ range n \ S := by simp [h0]; omega
  have hUcard : U.card = n - S.card - 1 := by
    rw [hU, card_erase_of_mem h0U, card_sdiff_of_subset hS, card_range]
  have hs1 : S.card + 1 ≤ n := by
    have hsub : S ⊆ (range n).erase 0 := fun x hx => mem_erase.2 ⟨fun h => h0 (h ▸ hx), hS hx⟩
    have := card_le_card hsub
    rw [card_erase_of_mem (by simp; omega), card_range] at this
    omega
  have key : ∑ T' ∈ U.powerset, δ ^ T'.card * (1 - δ) ^ (U.card - T'.card) = 1 := by
    rw [sum_pow_mul_eq_add_pow]; simp
  have step1 : condProb n δ (fun T => Disjoint S T) =
      ∑ T ∈ (range n).powerset.filter (fun T => 0 ∈ T ∧ Disjoint S T),
        δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) := by
    unfold condProb
    rw [sum_filter]
    refine sum_congr rfl (fun T _ => ?_)
    split_ifs <;> rfl
  have step2 : ∑ T ∈ (range n).powerset.filter (fun T => 0 ∈ T ∧ Disjoint S T),
        δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) =
      ∑ T' ∈ U.powerset, δ ^ T'.card * ((1 - δ) ^ S.card * (1 - δ) ^ (U.card - T'.card)) := by
    refine sum_nbij' (fun T => T.erase 0) (fun T' => insert 0 T') ?_ ?_ ?_ ?_ ?_
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT ⊢
      obtain ⟨hTn, _, hST⟩ := hT
      intro x hx
      rw [mem_erase] at hx
      rw [hU, mem_erase, mem_sdiff]
      exact ⟨hx.1, hTn hx.2, fun hxS => disjoint_left.1 hST hxS hx.2⟩
    · intro T' hT'
      simp only [mem_filter, mem_powerset] at hT' ⊢
      refine ⟨?_, mem_insert_self _ _, ?_⟩
      · intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · simp; omega
        · exact (mem_sdiff.1 (mem_of_mem_erase (hT' hx))).1
      · rw [disjoint_insert_right]
        refine ⟨h0, ?_⟩
        rw [disjoint_left]
        intro x hxS hxT
        exact (mem_sdiff.1 (mem_of_mem_erase (hT' hxT))).2 hxS
    · intro T hT
      simp only [mem_powerset, mem_filter] at hT
      exact insert_erase hT.2.1
    · intro T' hT'
      simp only [mem_powerset] at hT'
      apply erase_insert
      intro h
      have := hT' h
      rw [hU] at this
      exact (notMem_erase 0 _) this
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      obtain ⟨hTn, h0T, hST⟩ := hT
      have hsub : T.erase 0 ⊆ U := by
        intro x hx
        rw [mem_erase] at hx
        rw [hU, mem_erase, mem_sdiff]
        exact ⟨hx.1, hTn hx.2, fun hxS => disjoint_left.1 hST hxS hx.2⟩
      have hc := card_le_card hsub
      rw [card_erase_of_mem h0T] at hc ⊢
      have hT1 : 1 ≤ T.card := card_pos.2 ⟨0, h0T⟩
      rw [← pow_add]
      congr 2
      omega
  rw [step1, step2]
  simp_rw [mul_left_comm _ ((1 - δ) ^ S.card)]
  rw [← mul_sum, key, mul_one]
end Formalism.G0.TopsConditionalProbabilityBounds
