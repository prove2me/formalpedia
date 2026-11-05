-- Prove2me | solution 1 for ClauseBound.ParityChecks.TopOL.sq_le_tauOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:58.299124+00:00
-- url     : https://prove2.me/submissions/84300635-8bcc-4788-92f3-2575abe6346f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace ClauseBound.ParityChecks.TopOL
theorem _root_.solution {k s : ℕ} (h : k ≤ s) : k ^ 2 ≤ tauOf s := by
  calc k ^ 2 ≤ (2 ^ s) ^ 2 := Nat.pow_le_pow_left (h.trans Nat.lt_two_pow_self.le) 2
    _ = 2 ^ (s * 2) := (pow_mul 2 s 2).symm
    _ ≤ 2 ^ (4 * s + 17) := Nat.pow_le_pow_right (by norm_num) (by omega)
end ClauseBound.ParityChecks.TopOL
