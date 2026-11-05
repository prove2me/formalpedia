-- Prove2me | solution 1 for ClauseBound.Gen.Pick.pow_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:42.055424+00:00
-- url     : https://prove2.me/submissions/e46719fd-1e7e-44f0-b34f-c9882e3be9f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_ClauseBound_Gen_Pick_g_le_K_succ
import Theorems.Thm_ClauseBound_Gen_Pick_pow_le_g
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
namespace ClauseBound.Gen.Pick
theorem _root_.solution (x₀ l : ℕ) : 2 ^ (3 * l + x₀) ≤ 8 * K x₀ l := by
  cases l with
  | zero =>
    have : K x₀ 0 = 2 ^ x₀ := rfl
    rw [this, Nat.mul_zero, Nat.zero_add]; omega
  | succ l =>
    have h1 : 2 ^ (3 * (l + 1) + x₀) = 8 * 2 ^ (3 * l + x₀) := by ring
    rw [h1]
    exact Nat.mul_le_mul_left 8 ((pow_le_g x₀ l).trans (g_le_K_succ x₀ l))
end ClauseBound.Gen.Pick
