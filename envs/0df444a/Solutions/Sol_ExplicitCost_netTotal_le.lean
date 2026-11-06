-- Prove2me | solution 1 for ExplicitCost.netTotal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:03.969222+00:00
-- url     : https://prove2.me/submissions/eade7c5e-caaa-41a2-8338-135023213e14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {n : ℕ} (N : Net n) {P B : ℕ} (hN : N.Is P B) : N.U ≤ n * P := by
  unfold Net.U
  calc ∑ a, ∑ b ∈ univ.erase a, N.c a b ≤ ∑ _a : Fin n, P := Finset.sum_le_sum fun a _ => hN.i a
    _ = n * P := by rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
end ExplicitCost
