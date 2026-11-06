-- Prove2me | solution 1 for Exits.foldUntil_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:08.832267+00:00
-- url     : https://prove2.me/submissions/cc627cee-b169-4888-8277-ee3c922be796

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
import Theorems.Thm_Exits_foldUntil_body
import Theorems.Thm_Exits_met_cons_of_go
import Theorems.Thm_Exits_met_cons_of_stop
import Theorems.Thm_Exits_met_nil
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
open Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}
namespace Exits
theorem _root_.solution {xs : List τ} {o : Option τ} (ho : Orbit nxt o xs) (t : τ → ℕ) (v : τ → β) (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ met (fun c x => g c x (v x)) stop c xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ met (fun c x => g c x (v x)) stop c xs, size x ≤ Sx)
    (hc : ∀ l, l <+: met (fun c x => g c x (v x)) stop c xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldUntil start nxt M g stop c₀).Reaches (Sx + (Sc + Sm) + 1) ((met (fun c x => g c x (v x)) stop c xs).foldl (fun c x => g c x (v x)) c)
      (foldGo M c o) ((met (fun c x => g c x (v x)) stop c xs).map fun x => t x + 1).sum := by
  induction ho generalizing c with
  | nil =>
    have := hc [] List.nil_prefix
    rw [met_nil]
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at this; omega)
  | @cons x xs _ ih =>
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    cases hs : stop (g c x (v x)) with
    | true =>
      have e : met (fun c x => g c x (v x)) stop c (x :: xs) = [x] := met_cons_of_stop hs xs
      rw [e] at hM hx hc ⊢
      have h1 := hx x List.mem_cons_self
      have h3 := hc [x] List.prefix_rfl
      simp only [List.foldl_cons, List.foldl_nil] at h3
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldl_cons, List.foldl_nil]
      refine foldUntil_body (hM x List.mem_cons_self) (by omega) ?_
      rw [hs, if_pos rfl]
      exact .halt rfl (by change size (g c x (v x)) + 1 ≤ _; omega)
    | false =>
      have e : met (fun c x => g c x (v x)) stop c (x :: xs) = x :: met (fun c x => g c x (v x)) stop (g c x (v x)) xs := met_cons_of_go hs xs
      rw [e] at hM hx hc ⊢
      have h1 := hx x List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      refine foldUntil_body (hM x List.mem_cons_self) (by omega) ?_
      rw [hs, if_neg Bool.false_ne_true]
      exact ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl)
end Exits
