-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.choose_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:00.19612+00:00
-- url     : https://prove2.me/submissions/20c24f67-b21b-48c4-8fb8-582e385cef69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_factorial_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_descFactorial_polyT
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_div
attribute [local fun_prop] Groundwork.PolyT.div



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n k : α → ℕ} (hn : PolyT n) (hk : Unary k) : PolyT fun x => (n x).choose (k x) :=
  (PolyT.div (descFactorial_polyT hn hk) (factorial_polyT hk)).congr fun _ => (Nat.choose_eq_descFactorial_div_factorial _ _).symm
end ClauseBound.ParityChecks.CertLib
