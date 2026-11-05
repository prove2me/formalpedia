-- Prove2me | solution 1 for ClauseBound.Inst.Half.zzF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:31:15.882295+00:00
-- url     : https://prove2.me/submissions/5bccc40b-becd-4579-b265-377dd1f924de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabBot_prod_toFinset_coe
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution (ν : List ℕ) : zzF ν = ClauseBound.Boson.zz (ν : Multiset ℕ) := by
  rw [zzF, ← HalfTabBot.prod_toFinset_coe ν fun k => ((k ^ ν.count k * factN (ν.count k) : ℕ) : ℤ), ← Nat.cast_prod, Int.natAbs_natCast, zz]
  exact Finset.prod_congr rfl fun k _ => by rw [factN_eq, Multiset.coe_count]
end ClauseBound.Inst.Half
