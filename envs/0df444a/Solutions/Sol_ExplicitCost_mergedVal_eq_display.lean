-- Prove2me | solution 1 for ExplicitCost.mergedVal_eq_display
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:10.568803+00:00
-- url     : https://prove2.me/submissions/3ed92690-9dbb-4a9c-b32a-18ac165065c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost
import Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
import Theorems.Thm_Eight_ViaGrouping_groupedTables_eq_display
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_toInst_eq_mergedVal
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ)
    (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (θ : Fin K → List Bool) (hθ : ∀ γ', γ' ≠ γ → (θ γ').length = L) :
    mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (γ.val, List.ofFn θ)) = display Np c N hK0 x γ θ := by
  rw [← groupedTables_eq_display h hK0 x L hY γ θ hθ, Paper.groupedTables, toInst_eq_mergedVal Np.toPaperNetwork hK0 (Table.isPaperNetwork h).presented x L γ θ hθ]
end ExplicitCost
