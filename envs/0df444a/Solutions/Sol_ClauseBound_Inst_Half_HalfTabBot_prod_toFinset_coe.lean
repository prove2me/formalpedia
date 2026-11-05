-- Prove2me | solution 1 for ClauseBound.Inst.Half.HalfTabBot.prod_toFinset_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:04.960915+00:00
-- url     : https://prove2.me/submissions/0c13387c-b31f-432e-a6f4-913b5e097deb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabBot
namespace ClauseBound.Inst.Half.HalfTabBot
theorem _root_.solution (ν : List ℕ) (g : ℕ → ℤ) : ∏ k ∈ (ν : Multiset ℕ).toFinset, g k = (ν.dedup.map g).prod := by
  have h : (ν : Multiset ℕ).toFinset.val = (ν.dedup : Multiset ℕ) := by rw [Multiset.toFinset_val, Multiset.coe_dedup]
  rw [Finset.prod_eq_multiset_prod, h, Multiset.map_coe, Multiset.prod_coe]
end ClauseBound.Inst.Half.HalfTabBot
