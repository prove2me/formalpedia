-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.mod_two_pow_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:47.783224+00:00
-- url     : https://prove2.me/submissions/0302d053-ec6f-476c-9719-6e05ab3da0e9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_modZ_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x % 2 ^ k x :=
  (modZ_polyT ha (PolyT.pow_unary (PolyT.const 2) hk)).congr fun x => by push_cast; rfl
end ClauseBound.ParityChecks.CertLib
