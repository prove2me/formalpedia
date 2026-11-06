-- Prove2me | solution 1 for ExplicitCost.answerCall_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:10.26323+00:00
-- url     : https://prove2.me/submissions/0c382423-5311-4c1e-bd85-14a8c1ab24f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_Achievable
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingLemma
import Theorems.Thm_ExplicitCost_clique_groupW
import Theorems.Thm_ExplicitCost_Mirrors_mapIn
import Theorems.Thm_ExplicitCost_inB_groupingInput
import Theorems.Thm_ExplicitCost_inG_groupingInput
import Theorems.Thm_ExplicitCost_inK_groupingInput
import Theorems.Thm_ExplicitCost_inP_groupingInput
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size
import Theorems.Thm_Printed_mapIn_within
import Theorems.Thm_Printed_tables_eq_some


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes
namespace ExplicitCost
theorem _root_.solution (hL : LabelLengthIsL) (hSlow : QueryMachines.StSlowDown) (hSub : QueryMachines.StSubstWithin) {c₁ : ℕ} {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α)
    {a b K g : ℕ} (hK0 : 0 < K) {N : Net g} {P B τ 𝒯 SE x : ℕ} (hb : 0 < b) (hab : a ≤ b) (hN : N.Is P B)
    (hE : SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE)
    (hentry : ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * AppRunningTime.Lof K g ((a : ℝ) / b) P N.U),
      entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
        ((Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).W γ Θ) ∧
      |(Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).W γ Θ| < 2 ^ bitsOut K g P B) :
    (answerCall E arg).Within (netOracle N) (fun _ => τ) (groupingInput a b K N P B, callOf (groupingInput a b K N P B, x)) (𝒯 * (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ + 2))
      (size (groupingInput a b K N P B, x) + SE + (g * (P + B)) ^ c₁ + 1) (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value := by
  obtain ⟨hLL, hBB⟩ := hL a b K g N P B hb hab hK0 hN
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = AppRunningTime.Lof K g ((a : ℝ) / b) P N.U := ⟨_, rfl⟩
  rw [← hLdef] at hLL hE hentry ⊢
  rw [← hBB] at hE
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ := ⟨_, rfl⟩
  rw [← ht] at hentry ⊢
  -- E on the tables of the clique of the groups
  have hrun := hE (groupW N P B hK0 x L) fun w hw z hz => by
    unfold groupW
    rw [dif_pos hw]
    exact (hentry ⟨w, hw⟩ z hz).2
  rw [clique_groupW] at hrun
  have hslow := hSlow _ _ _ _ E _ _ 𝒯 SE (t + 2) _ (by omega) hrun
  -- each query answered by computing the entry
  have hsub := hSub _ _ _ _ (GroupingInput × ℕ) _ _ E (QueryMachine.mapIn entryInput entryData) (tables K L (groupW N P B hK0 x L)) (netOracle N) (fun _ => t + 2) (fun _ => τ)
    (groupingInput a b K N P B, x) _ _ SE ((g * (P + B)) ^ c₁) _ (fun _ => t) hslow
    (fun q v hq => mapIn_within (by
      obtain ⟨hq1, hq2, rfl⟩ := tables_eq_some hq
      change entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists (inK (groupingInput a b K N P B)) (labelLength (groupingInput a b K N P B)) q) _ _ _
      rw [inK_groupingInput, hLL]
      unfold groupW
      rw [dif_pos hq1]
      exact (hentry ⟨q.1, hq1⟩ q.2 hq2).1))
    (fun _ => le_rfl)
  refine mapIn_within ?_
  change (E.subst (QueryMachine.mapIn entryInput entryData)).Within (netOracle N) (fun _ => τ)
    ((groupingInput a b K N P B, x), arg (unary (inK (groupingInput a b K N P B)), unary (labelLength (groupingInput a b K N P B)),
      unary (bitsOut (inK (groupingInput a b K N P B)) (inG (groupingInput a b K N P B)) (inP (groupingInput a b K N P B)) (inB (groupingInput a b K N P B))))) _ _ _
  rw [inK_groupingInput, inG_groupingInput, inP_groupingInput, inB_groupingInput, hLL]
  exact hsub
end ExplicitCost
