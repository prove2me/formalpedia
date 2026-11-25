-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:22.467603+00:00
-- url     : https://prove2.me/submissions/655793a8-c80d-44c4-9085-e90db9498a11

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_d_le_one
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_c_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Wt_le
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_prod_wP
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_sum_event
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_comb
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_WF_init
import Theorems.Thm_P2M_Formalism_G0_TopsWeightFunctionBounds_Phi_init__f265b99736a1
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_term_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution : TopsChoiceSecondBound := by
  intro n δ L₂ r N₁ hn hev hδ hL hLδ hr hN
  have h1 := d_le_one hδ hL hLδ
  have hR : 1 ≤ 3 * r := by omega
  have hk1 : 0 < N₁ / (3 * r) := Nat.div_pos hN (by omega)
  have hK : 1 + 3 * r * (N₁ / (3 * r) - 1) ≤ N₁ := by
    have a1 : 3 * r * (N₁ / (3 * r)) ≤ N₁ := Nat.mul_div_le N₁ (3 * r)
    have a2 : 3 * r * (N₁ / (3 * r) - 1) + 3 * r = 3 * r * (N₁ / (3 * r)) := by
      rw [← mul_add_one]; congr 1; omega
    generalize 3 * r * (N₁ / (3 * r) - 1) = X at a2 ⊢
    generalize 3 * r * (N₁ / (3 * r)) = Y at a1 a2
    omega
  have hq : (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) = 1 - aF L₂ δ ^ (3 * r) := by
    unfold aF; rw [mul_pow]
  rw [hq]
  have hc0 : 0 ≤ 1 - aF L₂ δ ^ (3 * r) := c_nonneg hδ hLδ
  rcases hδ.eq_or_lt with hδ0 | hδpos
  · have hz : condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) = 0 := by
      unfold condProb
      apply Finset.sum_eq_zero
      intro T _
      split_ifs with h
      · have : 2 ≤ T.card := by have := h.2.2; omega
        rw [← hδ0, zero_pow (by omega), zero_mul]
      · rfl
    rw [hz]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc0 _)
  · apply le_of_mul_le_mul_left _ hδpos
    set K := N₁ / (3 * r) - 1 with hKdef
    have step1 : δ * condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤
        ∑ i ∈ Finset.range n, ∑ T ∈ (Finset.range n).powerset,
          (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i)))
              ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) := by
      rw [Finset.sum_comm]
      unfold condProb
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro T hT
      split_ifs with hA
      · obtain ⟨i, hi, hiT, hrun⟩ := comb (by omega) hev hr K hK T hA.2.1
        have hprod := prod_wP (δ := δ) n T (Finset.mem_powerset.1 hT)
        have hc : 1 ≤ T.card := Finset.card_pos.2 ⟨0, hA.1⟩
        have hle : (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i)))
              ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) ≤
            ∑ j ∈ Finset.range n, (if j ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even j)))
              ((Lst n j).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) :=
          Finset.single_le_sum (f := fun j => if j ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even j)))
              ((Lst n j).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0)
            (fun j _ => term_nonneg hδ h1 _ T n) (Finset.mem_range.2 hi)
        rw [if_pos ⟨hiT, hrun⟩] at hle
        calc δ * (δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card))
            = ∏ p ∈ Finset.range n, wP δ T p := by
              rw [hprod, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hc]
          _ ≤ _ := hle
      · rw [mul_zero]
        exact Finset.sum_nonneg (fun j _ => term_nonneg hδ h1 _ T n)
    have step2 : ∑ i ∈ Finset.range n, ∑ T ∈ (Finset.range n).powerset,
          (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i)))
              ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) ≤
        ∑ i ∈ Finset.range n, δ * (1 - aF L₂ δ ^ (3 * r)) ^ K := by
      apply Finset.sum_le_sum
      intro i hi
      rw [sum_event (Finset.mem_range.1 hi)]
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (Wt_le hδ hL hLδ hR (n - 1) _ (WF_init hR K _)).trans (Phi_init' hδ hL hLδ hR K _)
    calc δ * condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤ _ := step1
      _ ≤ _ := step2
      _ = δ * (n * (1 - aF L₂ δ ^ (3 * r)) ^ K) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
end Formalism.G0.TopsWeightFunctionBounds
