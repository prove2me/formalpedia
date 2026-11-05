-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.clog_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:46:42.257237+00:00
-- url     : https://prove2.me/submissions/25c6cee8-078c-43a1-95ca-edf3682e37ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_congr
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_two_eq
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_congr
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_length
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n : α → ℕ} (hn : PolyT n) : Unary fun x => Nat.clog 2 (n x) :=
  unary_congr (Unary.of_length (PolyT.bits (PolyT.sub hn (PolyT.const 1)))) fun x => by rw [Nat.size_eq_bits_len, clog_two_eq]
end ClauseBound.ParityChecks.CertLib
