-- Prove2me | solution 1 for ExplicitCost.groupClique_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:33:11.380217+00:00
-- url     : https://prove2.me/submissions/d1457fbb-1c7b-440f-b188-afd8467ec32c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma
import Theorems.Thm_Printed_asked_isNetworkP


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hV : ValueIsKept) {K n : ℕ} (hK0 : 0 < K) (N : Net n) {P B : ℕ} (hN : N.Is P B) (x L : ℕ) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) :
    (Value.groupClique asked.under (netInput N P B) N hK0 x L).value = N.value :=
  hV NetInput n K hK0 (asked.close (netOracle N)) (netInput N P B) N P B 1 _ (asked_isNetworkP N hN) x L hY
end ExplicitCost
