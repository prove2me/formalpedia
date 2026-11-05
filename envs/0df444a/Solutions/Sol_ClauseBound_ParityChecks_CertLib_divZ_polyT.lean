-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.divZ_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:35.581915+00:00
-- url     : https://prove2.me/submissions/812249ce-402b-40e7-80b7-379085672976

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_ediv_natCast
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x / (b x : ℤ) := by
  have h1 : PolyT fun x => (a x).toNat / b x := PolyT.div (PolyT.toNat ha) hb
  have h2 : PolyT fun x => ((a x).natAbs - 1) / b x + 1 := PolyT.add (PolyT.div (PolyT.sub (PolyT.natAbs ha) (PolyT.const 1)) hb) (PolyT.const 1)
  exact (PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) ha) (PolyT.natCast h1)
    (PolyT.ite' (PolyT.decide_eq hb (PolyT.const 0)) (PolyT.const 0) (PolyT.negZ (PolyT.natCast h2)))).congr fun x => (ediv_natCast _ _).symm
end ClauseBound.ParityChecks.CertLib
