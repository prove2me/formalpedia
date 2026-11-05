-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.getD2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:11:43.400947+00:00
-- url     : https://prove2.me/submissions/bf4254b7-4940-4230-9362-b5eaa3a9e0d6

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
theorem _root_.solution {a b c : ℕ} (ha : a ≤ c) (hb : b ≤ c) : ∀ l < 2, [a, b].getD l 0 ≤ c := by
  intro l hl
  interval_cases l
  · exact ha
  · exact hb
end ClauseBound.ParityChecks.Count
