-- Prove2me | solution 1 for ClauseBound.Inst.Half.RcolF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:29:48.062846+00:00
-- url     : https://prove2.me/submissions/0282e15e-db1d-4618-8d19-2576fde22b4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Theorems.Thm_ClauseBound_Inst_Half_pTab_polyT
import Theorems.Thm_ClauseBound_Inst_Half_pzF_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half
theorem _root_.solution {h : α → ℕ} {s : α → ℤ} (hh : Unary h) (hs : PolyT s) : PolyT fun x => RcolF (h x) (s x) := by
  have hT : PolyT fun x => pTab (4 * h x) := pTab_polyT ((Unary.const 4).mul hh)
  have hr : PolyT fun x => List.range (2 * h x + 1) := PolyT.range (((Unary.const 2).mul hh).add (Unary.const 1))
  have hh' : PolyT fun q : α × ℕ => ((h q.1 : ℕ) : ℤ) := PolyT.natCast (PolyT.comp hh.poly PolyT.id'.fst)
  have hf : PolyT fun q : α × ℕ => pzF (pTab (4 * h q.1)) (2 * (h q.1 : ℤ) - s q.1 - (q.2 : ℤ)) :=
    pzF_polyT (PolyT.comp (f := fun x => pTab (4 * h x)) hT PolyT.id'.fst)
      (PolyT.subZ (PolyT.subZ (PolyT.mulZ (PolyT.const 2) hh') (PolyT.comp hs PolyT.id'.fst)) (PolyT.natCast PolyT.id'.snd))
  unfold RcolF
  exact PolyT.sum (PolyT.map hf hr)
end ClauseBound.Inst.Half
