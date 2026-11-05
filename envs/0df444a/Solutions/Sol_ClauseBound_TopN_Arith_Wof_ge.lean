-- Prove2me | solution 1 for ClauseBound.TopN.Arith.Wof_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:26:58.187444+00:00
-- url     : https://prove2.me/submissions/b6a6563d-e099-434d-b17f-9222a354ca00

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s C₀ : ℕ}
namespace ClauseBound.TopN.Arith
theorem _root_.solution (hK : 1 ≤ K) : (betaN k s + 3) * 2 ^ betaN k s ≤ Wof k K s ∧ (betaN k s + 3) ^ 2 * K.size ≤ Wof k K s ∧
    (betaN k s + 3) ^ 2 ≤ Wof k K s ∧ (betaN k s + 3) * K.size ≤ Wof k K s ∧ K.size ≤ Wof k K s ∧ betaN k s + 3 ≤ Wof k K s ∧ 2 ^ betaN k s ≤ Wof k K s ∧ 1 ≤ Wof k K s := by
  unfold Wof
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK
  have hD : 1 ≤ 2 ^ betaN k s := Nat.one_le_two_pow
  generalize K.size = Y at hY
  generalize 2 ^ betaN k s = D at hD
  have hb : 1 ≤ betaN k s + 3 := by omega
  generalize betaN k s + 3 = b at hb
  have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have m1 : b * D ≤ b ^ 2 * D * Y := by
    calc b * D ≤ b ^ 2 * D := Nat.mul_le_mul_right _ hbb
      _ ≤ b ^ 2 * D * Y := Nat.le_mul_of_pos_right _ hY
  have m2 : b ^ 2 * Y ≤ b ^ 2 * D * Y := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hD)
  have m3 : b ^ 2 ≤ b ^ 2 * Y := Nat.le_mul_of_pos_right _ hY
  have m4 : b * Y ≤ b ^ 2 * Y := Nat.mul_le_mul_right _ hbb
  have m5 : Y ≤ b ^ 2 * Y := Nat.le_mul_of_pos_left _ h1
  have m6 : D ≤ b * D := Nat.le_mul_of_pos_left _ hb
  exact ⟨m1, m2, m3.trans m2, m4.trans m2, m5.trans m2, (hbb.trans m3).trans m2, m6.trans m1, (h1.trans m3).trans m2⟩
end ClauseBound.TopN.Arith
