-- Prove2me | solution 1 for Eight.Level.Cert.numPat8_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:29:17.531652+00:00
-- url     : https://prove2.me/submissions/c7a4cfc6-ba10-4864-bc87-5400d6c21452

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_Eight_Level_Cert
import Theorems.Thm_Eight_Level_Cert_tOf_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped
open Eight.Level.Cert
variable {C : Type} [Enc C] {lam : C → ℕ}
namespace Eight.Level.Cert
theorem _root_.solution (g : ℕ) (hl : Unary lam) : PolyT (numPat8 g lam) :=
  pow_polyT ((tOf_unary hl).add (Unary.const 1)).poly (Unary.const (nRect g))
end Eight.Level.Cert
