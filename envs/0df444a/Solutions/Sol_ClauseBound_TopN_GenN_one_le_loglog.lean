-- Prove2me | solution 1 for ClauseBound.TopN.GenN.one_le_loglog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:40:56.578983+00:00
-- url     : https://prove2.me/submissions/07223622-c423-4acb-bc78-6e069d27c574

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Theorems.Thm_ClauseBound_TopN_GenN_two_le_log
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.GenN
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith
namespace ClauseBound.TopN.GenN
theorem _root_.solution (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) := by
  have h := two_le_log n
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  exact h
end ClauseBound.TopN.GenN
