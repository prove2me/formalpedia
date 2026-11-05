-- Prove2me | solution 1 for Eight.ViaGrouping.Table.tableM_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:41:56.373196+00:00
-- url     : https://prove2.me/submissions/14d8b6e1-373a-4bd4-a078-7bd386039bb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_stLen_le
import Theorems.Thm_Eight_ViaGrouping_Table_size_query_le
import Theorems.Thm_Eight_ViaGrouping_Table_termP_runs
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_NetE_stLen_le
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_natAbs_prod_le
import Theorems.Thm_Groundwork_Stepped_prodRange_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_PaddedDescent_F_RebalF_stLen_le
import Theorems.Thm_Paper_Achievable_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (m : ℕ) (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    (tableM K g Np).Runs ((c, x), (G.val, List.ofFn θ)) (2 ^ (P * m) * (g * g * (4 * τ + 4) + 1))
      (S + 4 * (size c + size x + size K + K * (2 * β + 2)) + 5 * (P * m) + 2 * (B * (g * g)) + 3 * size (g * g) + 30)
      (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))) := by
  have hsu := size_query_le (c := c) (x := x) hθ hG
  have hst : stLen K g Np.toPaperNetwork c x G ≤ P * m := stLen_le h (hm G G.2)
  cases hv : validB K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) with
  | false =>
    have ev : mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) = 0 := by
      simp only [mergedVal, hv, if_false, Bool.false_eq_true]
    rw [ev]
    refine (ite_runs_false hv (const_runs (0 : ℤ) _)).mono (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _))) ?_
    have : size (0 : ℤ) = 1 := rfl
    omega
  | true =>
    have ev : mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) = ∑ y ∈ range (nStates K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ))),
        ∏ i ∈ range (g * g), termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) := by
      simp only [mergedVal, hv, if_true]
    rw [ev]
    have eN : nStates K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) = 2 ^ stLen K g Np.toPaperNetwork c x G := rfl
    have hin : ∀ y < nStates K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)), (prodRange (nPairs g) (termP K g Np)).Runs (((c, x), (G.val, List.ofFn θ)), y)
        (g * g * (4 * τ + 3 + 1))
        (3 * (size ((c, x), (G.val, List.ofFn θ)) + (stLen K g Np.toPaperNetwork c x G + 1)) + 3 * size (g * g) + B * (g * g) + S + 15)
        (∏ i ∈ range (g * g), termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) := by
      intro y hy
      have hy' : y.size ≤ stLen K g Np.toPaperNetwork c x G := Nat.size_le.2 (eN ▸ hy)
      have := prodRange_runs (N := nPairs g) (M := termP K g Np) (a := (((c, x), (G.val, List.ofFn θ)), y))
        (fun _ => 4 * τ + 3) (fun i => termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) (2 ^ B)
        (2 * (size (((c, x), (G.val, List.ofFn θ)), y) + size (g * g)) + S + 12) Nat.one_le_two_pow
        (fun i hi => (termP_runs h hβ hθ y hi).1.mono le_rfl (by
          have := Nat.size_le_size (Nat.le_of_lt hi)
          simp only [nPairs] at this
          simp only [size_prod, size_nat] at this ⊢
          omega))
        (fun i hi => (termP_runs h hβ hθ y hi).2)
      refine this.mono (by simp [nPairs]) ?_
      simp only [nPairs, ← pow_mul]
      simp only [size_prod, size_nat, Nat.size_pow] at hsu ⊢
      omega
    have hout := sumRange_runs (N := nStates K g Np.toPaperNetwork) (a := ((c, x), (G.val, List.ofFn θ))) (fun _ => g * g * (4 * τ + 3 + 1))
      (fun y => ∏ i ∈ range (g * g), termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) ((2 ^ B) ^ (g * g)) _ hin
      (fun y _ => natAbs_prod_le _ _ _ fun i hi => (termP_runs h hβ hθ y hi).2)
    refine (ite_runs_true hv hout).mono ?_ ?_
    · rw [sum_const, card_range, smul_eq_mul, eN]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hst) le_rfl
    · rw [eN, ← pow_mul, ← pow_add]
      simp only [size_nat, Nat.size_pow] at hsu ⊢
      omega
end Eight.ViaGrouping.Table
