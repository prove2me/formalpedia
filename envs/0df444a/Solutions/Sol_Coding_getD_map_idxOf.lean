-- Prove2me | solution 1 for Coding.getD_map_idxOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:39:31.341789+00:00
-- url     : https://prove2.me/submissions/9ad152a1-3056-4a85-b329-505338591293

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution {α : Type} [BEq α] [LawfulBEq α] (f : α → Bool) {l : List α} {x : α} (hx : x ∈ l) : (l.map f).getD (l.idxOf x) false = f x := by
  have h := List.idxOf_lt_length_of_mem hx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h, List.getElem_idxOf h]
  rfl
end Coding
