-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.getD3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:42.578554+00:00
-- url     : https://prove2.me/submissions/d4f8a093-a505-441d-b316-442caab7b998

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution {a b d c : ℕ} (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) : ∀ l < 3, [a, b, d].getD l 0 ≤ c := by
  intro l hl
  interval_cases l
  · exact ha
  · exact hb
  · exact hd
end ClauseBound.ParityChecks.Count
