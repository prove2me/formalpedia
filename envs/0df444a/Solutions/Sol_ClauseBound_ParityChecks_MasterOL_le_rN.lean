-- Prove2me | solution 1 for ClauseBound.ParityChecks.MasterOL.le_rN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:40.134392+00:00
-- url     : https://prove2.me/submissions/e2387bbc-d700-4e34-828f-caa9eb19a716

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Theorems.Thm_ClauseBound_Gen_End_one_le_log
import Theorems.Thm_ClauseBound_TopN_GenN_log_four_le
import Theorems.Thm_ClauseBound_TopN_GenN_one_le_loglog
import Theorems.Thm_ClauseBound_TopN_GenN_two_le_log
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.MasterOL
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN
namespace ClauseBound.ParityChecks.MasterOL
theorem _root_.solution {α : ℝ} {c : ℕ} (ha1 : α ≤ 1) (hc : 2 ≤ c) (n : ℕ) : 1 / ((c : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ c) ≤ SatK.rN 1 α n := by
  have hy := two_le_log n
  have hz := one_le_loglog n
  have hL := ClauseBound.Gen.End.one_le_log n
  have h4 := log_four_le n
  unfold SatK.rN
  set y := Real.logb 2 ((n : ℝ) + 4)
  set z := Real.logb 2 y
  set L := Real.logb 2 ((n : ℝ) + 2)
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hyα : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
  have h1 : y ^ α ≤ (c : ℝ) * L ^ c := by
    calc y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
      _ = y := Real.rpow_one y
      _ ≤ 2 * L := h4
      _ ≤ (c : ℝ) * L ^ c := by
          have : L ≤ L ^ c := le_self_pow₀ hL (by omega)
          nlinarith
  calc 1 / ((c : ℝ) * L ^ c) ≤ 1 / y ^ α := one_div_le_one_div_of_le hyα h1
    _ ≤ z ^ 1 / y ^ α := div_le_div_of_nonneg_right (by rw [pow_one]; exact hz) hyα.le
end ClauseBound.ParityChecks.MasterOL
