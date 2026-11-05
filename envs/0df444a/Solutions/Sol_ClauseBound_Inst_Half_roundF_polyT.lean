-- Prove2me | solution 1 for ClauseBound.Inst.Half.roundF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:29:24.03447+00:00
-- url     : https://prove2.me/submissions/5217bbe7-2454-4e38-bf89-021f6f34126d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Theorems.Thm_ClauseBound_Inst_Half_stepE_polyT
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
theorem _root_.solution {pad : α → U} {W k : α → ℕ} {old : α → PT} (hp : PolyT pad) (hW : Unary W) (hk : PolyT k) (ho : PolyT old) :
    PolyT fun x => roundF (pad x) (W x) (k x) (old x) := by
  unfold roundF
  exact foldl_cap (pad := pad) (l := fun x => List.range (W x + 1)) (a := fun _ => ([] : PT))
    (g := fun x new E => stepE (k x) (old x) new E) [] hp (PolyT.range (hW.add (Unary.const 1))) (PolyT.const _)
    (stepE_polyT (PolyT.comp hk PolyT.id'.fst) (PolyT.comp ho PolyT.id'.fst) PolyT.id'.snd.fst PolyT.id'.snd.snd)
end ClauseBound.Inst.Half
