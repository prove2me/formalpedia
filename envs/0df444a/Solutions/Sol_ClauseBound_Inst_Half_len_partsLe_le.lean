-- Prove2me | solution 1 for ClauseBound.Inst.Half.len_partsLe_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:42:04.020895+00:00
-- url     : https://prove2.me/submissions/7a4b751e-cf14-4afd-a7a7-388b38be7ed6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_len_le_of_forall
import Theorems.Thm_ClauseBound_Inst_Half_len_parts_le
import Theorems.Thm_ClauseBound_Part_length_partsLe_le
import Theorems.Thm_ClauseBound_Part_mem_partsLe
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution (E k : ℕ) : len (partsLe E k) ≤ p E * (7 * E + 4) + 2 := by
  have h1 := len_le_of_forall (c := 7 * E + 2) (partsLe E k) fun L hL => by
    obtain ⟨hs, hp, _⟩ := (mem_partsLe E k L).1 hL
    exact hs ▸ len_parts_le L fun n hn => (hp n hn).1
  have h2 : (partsLe E k).length * (7 * E + 2 + 2) ≤ p E * (7 * E + 4) := Nat.mul_le_mul_right _ (length_partsLe_le E k)
  omega
end ClauseBound.Inst.Half
