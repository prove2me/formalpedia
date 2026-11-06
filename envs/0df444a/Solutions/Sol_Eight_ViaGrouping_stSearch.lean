-- Prove2me | solution 1 for Eight.ViaGrouping.stSearch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:09.118253+00:00
-- url     : https://prove2.me/submissions/79f01128-aedb-4328-a8c3-0b26dee8eadd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Eight_ViaGrouping_goodP_iff
import Theorems.Thm_Eight_ViaGrouping_exists_goodP
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution : StSearch := by
  intro K hK C _ Np c N P B τ S h
  obtain ⟨x', hx', hgood'⟩ := exists_goodP hK h
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ (3 * K ^ 8))).find? (fun x => goodP K (3 * K ^ 8) Np (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodP K (3 * K ^ 8) Np (c, x) = true := List.find?_some (p := fun x => goodP K (3 * K ^ 8) Np (c, x)) hfind
  exact ⟨x, List.mem_range.1 (List.mem_of_find?_eq_some hfind), hfind, (goodP_iff _ h x).1 hgood⟩
end Eight.ViaGrouping
