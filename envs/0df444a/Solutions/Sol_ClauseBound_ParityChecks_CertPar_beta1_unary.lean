-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.beta1_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:20:10.677329+00:00
-- url     : https://prove2.me/submissions/a2a8cf9e-64f0-4769-a8db-abb0a3878170

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_choose_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_sup_range_unary_min
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
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
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution {m i : α → ℕ} (hm : PolyT m) (hi : Unary i) : Unary fun x => beta1 (m x) (i x) :=
  sup_range_unary_min (n := fun x => i x + 1) (f := fun x j => Nat.clog 2 ((m x).choose j)) (hi.add (Unary.const 1))
    (clog_unary (choose_polyT (PolyT.comp hm PolyT.id'.fst) (unary_min_right PolyT.id'.snd ((hi.add (Unary.const 1)).comp PolyT.id'.fst))))
end ClauseBound.ParityChecks.CertPar
