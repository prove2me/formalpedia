-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.log_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:43:17.874972+00:00
-- url     : https://prove2.me/submissions/51e67caa-4a73-4157-b7ad-9b79a17c4fe7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n : α → ℕ} (hn : PolyT n) : PolyT fun x => Nat.log 2 (n x) :=
  (PolyT.log2' hn).congr fun _ => Nat.log2_eq_log_two
end ClauseBound.ParityChecks.CertLib
