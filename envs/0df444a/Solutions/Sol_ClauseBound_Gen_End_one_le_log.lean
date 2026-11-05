-- Prove2me | solution 1 for ClauseBound.Gen.End.one_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:14:40.351147+00:00
-- url     : https://prove2.me/submissions/25c51aea-05df-4244-a897-e5013fb2f8de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Alg_Prog
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_End

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.End
namespace ClauseBound.Gen.End
theorem _root_.solution (m : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((m : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num
end ClauseBound.Gen.End
