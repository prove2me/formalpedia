-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.combineO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:32:42.10457+00:00
-- url     : https://prove2.me/submissions/73e3d76e-8226-4d08-b68c-e21bec64fd74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution {p n e q B c A d : ℝ} (hn : 0 ≤ n) (he : 0 ≤ e) (hq : 1 ≤ q) (hB : 0 ≤ B) (hc : 0 ≤ c) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (h : p ≤ B * n * e * q ∨ p ≤ c * (n * e) ∨ p ≤ A * (n * e) ∨ p ≤ d * (n * e)) : p ≤ (B + c + A + d) * n * e * q := by
  have hne : 0 ≤ n * e := mul_nonneg hn he
  have hbase : n * e ≤ n * e * q := le_mul_of_one_le_right hne hq
  have hT : 0 ≤ n * e * q := hne.trans hbase
  have t1 : 0 ≤ B * (n * e * q) := mul_nonneg hB hT
  have t2 : 0 ≤ c * (n * e * q) := mul_nonneg hc hT
  have t3 : 0 ≤ A * (n * e * q) := mul_nonneg hA hT
  have t4 : 0 ≤ d * (n * e * q) := mul_nonneg hd hT
  have e1 : (B + c + A + d) * n * e * q = B * (n * e * q) + c * (n * e * q) + A * (n * e * q) + d * (n * e * q) := by ring
  have e2 : B * n * e * q = B * (n * e * q) := by ring
  rw [e1]
  rcases h with h | h | h | h
  · rw [e2] at h; linarith
  · have := mul_le_mul_of_nonneg_left hbase hc; linarith
  · have := mul_le_mul_of_nonneg_left hbase hA; linarith
  · have := mul_le_mul_of_nonneg_left hbase hd; linarith
end ClauseBound.ParityChecks.ArithOL
