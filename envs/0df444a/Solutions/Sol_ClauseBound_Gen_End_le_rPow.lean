-- Prove2me | solution 1 for ClauseBound.Gen.End.le_rPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:39:42.960869+00:00
-- url     : https://prove2.me/submissions/aa4c1d56-c2b2-4099-8859-b49e1be3620d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Alg_Prog
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_End
import Theorems.Thm_ClauseBound_Gen_End_one_le_log
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.End
namespace ClauseBound.Gen.End
theorem _root_.solution {α : ℝ} {c : ℕ} (ha1 : α ≤ 1) (hc : 1 ≤ c) (m : ℕ) : 1 / ((c : ℝ) * Real.logb 2 ((m : ℝ) + 2) ^ c) ≤ SatM.rPow α m := by
  have hy := one_le_log m
  unfold SatM.rPow
  set y := Real.logb 2 ((m : ℝ) + 2)
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  refine one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _) ?_
  calc y ^ α ≤ y ^ (c : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (ha1.trans hc')
    _ = y ^ c := Real.rpow_natCast _ _
    _ ≤ (c : ℝ) * y ^ c := le_mul_of_one_le_left (by positivity) hc'
end ClauseBound.Gen.End
