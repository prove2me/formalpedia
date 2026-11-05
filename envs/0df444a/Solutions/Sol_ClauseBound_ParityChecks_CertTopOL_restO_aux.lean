-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.restO_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:57.075112+00:00
-- url     : https://prove2.me/submissions/78e3af4f-e8e6-4586-a94e-3c2823d1b965

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.pow_const



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {K n s D : α → ℕ}
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (k : ℕ) {Z₁ Z₂ B z q : α → ℕ} (hK : PolyT K) (h1 : PolyT Z₁) (h2 : PolyT Z₂) (hB : PolyT B) (hz : PolyT z) (hn : PolyT n) (hq : PolyT q) :
    PolyT fun x => 3 * K x ^ 8 * (3 * K x ^ 8) * 3 * Z₁ x + (3 * Z₂ x + 3 * z x + 12) + (n x / q x + 2) + (B x + 5 * k + 10 + (k + 3) * z x) := by
  have h8 : PolyT fun x => 3 * K x ^ 8 := (PolyT.const 3).mul (hK.pow_const 8)
  exact (((((h8.mul h8).mul (PolyT.const 3)).mul h1).add ((((PolyT.const 3).mul h2).add ((PolyT.const 3).mul hz)).add (PolyT.const 12))).add
    ((PolyT.div hn hq).add (PolyT.const 2))).add (((hB.add (PolyT.const (5 * k))).add (PolyT.const 10)).add ((PolyT.const (k + 3)).mul hz))
end ClauseBound.ParityChecks.CertTopOL
