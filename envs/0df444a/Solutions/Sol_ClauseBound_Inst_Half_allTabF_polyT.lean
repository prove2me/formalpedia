-- Prove2me | solution 1 for ClauseBound.Inst.Half.allTabF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:33:07.806783+00:00
-- url     : https://prove2.me/submissions/b1211816-af44-461a-8108-f8a203944c9f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Theorems.Thm_ClauseBound_Inst_Half_initT_polyT
import Theorems.Thm_ClauseBound_Inst_Half_roundF_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_foldl_cap
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half
theorem _root_.solution {pad : α → U} {W : α → ℕ} (hp : PolyT pad) (hW : Unary W) : PolyT fun x => allTabF (pad x) (W x) := by
  unfold allTabF
  exact foldl_cap (pad := pad) (l := fun x => List.range (W x)) (a := fun x => initT (W x))
    (g := fun x old k => roundF (pad x) (W x) (k + 1) old) [] hp (PolyT.range hW) (initT_polyT hW)
    (roundF_polyT (PolyT.comp hp PolyT.id'.fst) (hW.comp PolyT.id'.fst) (PolyT.add PolyT.id'.snd.snd (PolyT.const 1)) PolyT.id'.snd.fst)
end ClauseBound.Inst.Half
