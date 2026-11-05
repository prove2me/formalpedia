-- Prove2me | solution 1 for Eight.ViaGrouping.Table.mem_prs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:37.433412+00:00
-- url     : https://prove2.me/submissions/586aa489-dd83-45ad-8905-42f09b14b5c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping.Table
theorem _root_.solution {x G G' a b : ℕ} (ha : a ∈ members K g x G) (hb : b ∈ members K g x G') : (a, b) ∈ prs K g x G G' :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩
end Eight.ViaGrouping.Table
