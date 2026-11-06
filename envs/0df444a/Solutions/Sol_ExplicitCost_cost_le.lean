-- Prove2me | solution 1 for ExplicitCost.cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:46:41.88053+00:00
-- url     : https://prove2.me/submissions/fd659cd5-78ea-4a44-adee-80ce7d175d0a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
import Theorems.Thm_ExplicitCost_xi_facts
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {c g lam B tq T : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hT : T ≤ g * g * (askCost c lam + 1) ∨ T ≤ g * (tq + 1) ∨ T ≤ 1) : T ≤ (askCost c lam + tq) * Xi g lam B ^ (2 * c + 6) := by
  obtain ⟨h8, h1, h2, -, -, -, -⟩ := xi_facts hg hlam hB
  have ha : 2 ≤ askCost c lam := by unfold askCost; omega
  have hX : Xi g lam B ≤ Xi g lam B ^ (2 * c + 6) := Nat.le_self_pow (by omega) _
  refine le_trans ?_ (Nat.mul_le_mul_left _ hX)
  rcases hT with h | h | h
  · refine h.trans ?_
    calc g * g * (askCost c lam + 1) ≤ g * g * (2 * (askCost c lam + tq)) := Nat.mul_le_mul_left _ (by omega)
      _ = (askCost c lam + tq) * (2 * (g * g)) := by ring
      _ ≤ (askCost c lam + tq) * Xi g lam B := Nat.mul_le_mul_left _ h2
  · refine h.trans ?_
    calc g * (tq + 1) ≤ Xi g lam B * (askCost c lam + tq) := Nat.mul_le_mul h1 (by omega)
      _ = (askCost c lam + tq) * Xi g lam B := Nat.mul_comm _ _
  · exact h.trans (Nat.mul_pos (by omega) (by omega))
end ExplicitCost
