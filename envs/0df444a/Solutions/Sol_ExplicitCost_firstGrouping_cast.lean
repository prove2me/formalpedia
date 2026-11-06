-- Prove2me | solution 1 for ExplicitCost.firstGrouping_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:17.678085+00:00
-- url     : https://prove2.me/submissions/1558c884-28cc-49ec-996e-8a17dfc6ef6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hG : GroupingWithCall) (hL : LabelLengthIsL) {b K g n : ℕ} (hn : n = g) (hK0 : 0 < K) (N : Net n) {P B : ℕ} (hK : 2 ≤ K) (hg : 2 ≤ g) (hb : 1 ≤ b) (hN : N.Is P B)
    (hC : AppRunningTime.Cases K n ((1 : ℝ) / b) P N.c) {x : ℕ} (hx : (List.range (K ^ g)).find? (fun x' => goodData (((1, b), ((unary K, unary g), netInput N P B)), x')) = some x) :
    x < K ^ g ∧ (∀ γ : Fin K, K * #{v : Fin n | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧
      (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((1 : ℝ) / b) P N.U) ∧
      labelLength ((1, b), ((unary K, unary g), netInput N P B)) = AppRunningTime.Lof K g ((1 : ℝ) / b) P N.U := by
  subst hn
  obtain ⟨C, hG⟩ := hG
  have hC' : AppRunningTime.Cases K n (((1 : ℕ) : ℝ) / b) P N.c := by
    rw [Nat.cast_one]
    exact hC
  obtain ⟨x', hx', hf, h1, h2, -⟩ := hG 1 b K n hK0 N P B 0 hK hg Nat.one_pos hb hN hC'
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hf)
  have h3 := (hL 1 b K n N P B (by omega) hb hK0 hN).1
  rw [Nat.cast_one] at h2 h3
  exact ⟨hx', h1, h2, h3⟩
end ExplicitCost
