-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.bal_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:59.266608+00:00
-- url     : https://prove2.me/submissions/367b8e4b-b184-4011-a895-667a1fc5acea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_mod_two_pow_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_powZ_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {β : α → ℕ} {a : α → ℤ} (hβ : Unary β) (ha : PolyT a) : PolyT fun x => bal (β x) (a x) := by
  unfold bal
  have h1 : PolyT fun x => (2 : ℤ) ^ (β x - 1) := powZ_polyT (PolyT.const 2) (unary_sub hβ (PolyT.const 1))
  exact PolyT.subZ (mod_two_pow_polyT (PolyT.addZ ha h1) hβ) h1
end ClauseBound.ParityChecks.CertNum
