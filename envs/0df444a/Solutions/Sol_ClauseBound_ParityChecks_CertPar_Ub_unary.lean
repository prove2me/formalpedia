-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.Ub_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:16.283467+00:00
-- url     : https://prove2.me/submissions/120ae5f2-b409-41d4-a2c7-46cbadca84b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution (k : ℕ) {g n w β R : α → ℕ} (hg : Unary g) (hn : Unary n) (hw : Unary w) (hβ : Unary β) (hR : Unary R) :
    Unary fun x => Ub k (g x) (n x) (w x) (β x) (R x) :=
  ((Unary.const 2).mul hR).mul (((((Unary.const (k - 1)).mul hw).mul ((Unary.const 1).add hβ)).add ((Unary.const (k - 1)).mul (hn.add (Unary.const 1)))).add
    (unary_pow_const hg 2))
end ClauseBound.ParityChecks.CertPar
