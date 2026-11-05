-- Prove2me | solution 1 for ClauseBound.ParityChecks.Ev.Pb_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:51.10048+00:00
-- url     : https://prove2.me/submissions/6a2507a8-6e75-4275-8d7d-4cfc66a31b5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW
namespace ClauseBound.ParityChecks.Ev
theorem _root_.solution (g β D : ℕ) {n n' : ℕ} (hn : n ≤ n') : Pb g n β D ≤ Pb g n' β D := by
  unfold Pb qv
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.div_le_div_right (by omega)))
end ClauseBound.ParityChecks.Ev
