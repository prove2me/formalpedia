-- Prove2me | solution 1 for ClauseBound.TopN.leafC_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:27.448926+00:00
-- url     : https://prove2.me/submissions/34bba352-c016-4ccc-8061-e332c80d15fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_TopN_Budget
import Theorems.Thm_PaddedDescent_leafC_tauOf_le


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN
open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)
namespace ClauseBound.TopN
theorem _root_.solution (k s : ℕ) : leafC (tauOf s) k + 2 ≤ 2 ^ betaN k s := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  obtain ⟨E, hE⟩ : ∃ E, E = (4 * s + 17) * 2 ^ k := ⟨_, rfl⟩
  have hE1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have h2 : E + k + 1 ≤ betaN k s := by
    have e1 : (4 * s + 17) * (2 ^ (k + 1) + 1) = 2 * E + (4 * s + 17) := by rw [hE, pow_succ]; ring
    unfold betaN
    omega
  calc leafC (tauOf s) k + 2 ≤ 2 * (k * 2 ^ E) + 2 * 2 ^ E := Nat.add_le_add (hE ▸ leafC_tauOf_le k s) (by omega)
    _ = 2 * ((k + 1) * 2 ^ E) := by ring
    _ ≤ 2 * (2 ^ k * 2 ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ = 2 ^ (E + k + 1) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ betaN k s := Nat.pow_le_pow_right (by norm_num) h2
end ClauseBound.TopN
