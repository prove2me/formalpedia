-- Prove2me | solution 1 for ClauseBound.Inst.Half.nextP_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:24:41.240342+00:00
-- url     : https://prove2.me/submissions/c7027879-98e1-4f0a-9931-ca3ee66a11c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
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
theorem _root_.solution {T : α → List ℕ} (hT : PolyT T) : PolyT fun x => nextP (T x) := by
  have hT1 : PolyT fun q : α × ℕ => T q.1 := PolyT.comp hT PolyT.id'.fst
  have hT2 : PolyT fun r : (α × ℕ) × ℕ => T r.1.1 := PolyT.comp hT PolyT.id'.fst.fst
  have hv : PolyT fun r : (α × ℕ) × ℕ => r.1.2 + 1 := PolyT.add PolyT.id'.fst.snd (PolyT.const 1)
  have hk : PolyT fun r : (α × ℕ) × ℕ => r.2 + 1 := PolyT.add PolyT.id'.snd (PolyT.const 1)
  have hin : PolyT fun r : (α × ℕ) × ℕ => (r.1.2 + 1) * (T r.1.1).getD ((T r.1.1).length - (r.2 + 1) * (r.1.2 + 1)) 0 :=
    PolyT.mul hv (PolyT.getD hT2 (PolyT.sub hT2.length (PolyT.mul hk hv)) (PolyT.const 0))
  have hr : PolyT fun q : α × ℕ => List.range ((T q.1).length / (q.2 + 1)) :=
    PolyT.range (unary_div (Unary.of_length hT1) (PolyT.add PolyT.id'.snd (PolyT.const 1)))
  have hmid : PolyT fun q : α × ℕ => ((List.range ((T q.1).length / (q.2 + 1))).map fun k =>
      (q.2 + 1) * (T q.1).getD ((T q.1).length - (k + 1) * (q.2 + 1)) 0).sum := PolyT.sum (PolyT.map hin hr)
  unfold nextP
  exact PolyT.div (PolyT.sum (PolyT.map hmid (PolyT.range (Unary.of_length hT)))) hT.length
end ClauseBound.Inst.Half
