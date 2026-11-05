-- Prove2me | solution 1 for ClauseBound.ParityChecks.Ev.Ub_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:48.429203+00:00
-- url     : https://prove2.me/submissions/3dae0d1f-f3cc-4d7b-a91b-447ed9d6cd4c

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
theorem _root_.solution (k g β : ℕ) {n n' w w' R R' : ℕ} (hn : n ≤ n') (hw : w ≤ w') (h : R ≤ R') : Ub k g n w β R ≤ Ub k g n' w' β R' := by
  unfold Ub
  refine Nat.mul_le_mul (Nat.mul_le_mul_left _ h) (Nat.add_le_add_right (Nat.add_le_add ?_ ?_) _)
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw)
  · exact Nat.mul_le_mul_left _ (by omega)
end ClauseBound.ParityChecks.Ev
