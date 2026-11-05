-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.log_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:43:23.298071+00:00
-- url     : https://prove2.me/submissions/2aa8adf5-5611-42d7-94f3-2956acad85ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_log_polyT
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n : α → ℕ} (hn : Unary n) : Unary fun x => Nat.log 2 (n x) :=
  Unary.of_le hn (log_polyT hn.poly) fun _ => Nat.log_le_self _ _
end ClauseBound.ParityChecks.CertLib
