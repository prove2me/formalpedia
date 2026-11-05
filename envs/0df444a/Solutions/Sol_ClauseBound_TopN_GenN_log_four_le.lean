-- Prove2me | solution 1 for ClauseBound.TopN.GenN.log_four_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:30.374224+00:00
-- url     : https://prove2.me/submissions/24dec453-9973-4844-9c6a-015d92b42151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.GenN
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith
namespace ClauseBound.TopN.GenN
theorem _root_.solution (n : ℕ) : Real.logb 2 ((n : ℝ) + 4) ≤ 2 * Real.logb 2 ((n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℝ) + 4 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  calc Real.logb 2 ((n : ℝ) + 4) ≤ Real.logb 2 (((n : ℝ) + 2) ^ 2) := Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    _ = 2 * Real.logb 2 ((n : ℝ) + 2) := by rw [Real.logb_pow]; norm_num
end ClauseBound.TopN.GenN
