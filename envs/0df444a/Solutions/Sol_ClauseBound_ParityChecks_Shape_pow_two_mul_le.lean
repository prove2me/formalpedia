-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.pow_two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:55.391821+00:00
-- url     : https://prove2.me/submissions/b49a0c72-7666-469a-a59f-385ab42ef633

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (nb : ℕ) (h : 1 ≤ nb) : (1 + pr nb) ^ (2 * nb) ≤ 8 := by
  have hnb : (0 : ℝ) < nb := by exact_mod_cast h
  have h1 : (1 : ℝ) + 1 / nb ≤ Real.exp (1 / nb) := by
    have := Real.add_one_le_exp (1 / (nb : ℝ))
    linarith
  have h2 : ((1 : ℝ) + 1 / nb) ^ (2 * nb) ≤ Real.exp (1 / nb) ^ (2 * nb) := pow_le_pow_left₀ (by positivity) h1 _
  have h3 : Real.exp (1 / (nb : ℝ)) ^ (2 * nb) = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have h4 : Real.exp 1 ^ 2 ≤ 8 := by
    have h5 := Real.exp_one_lt_d9
    have h6 := Real.exp_pos 1
    nlinarith
  have h7 : (((1 + 1 / (nb : ℚ)) ^ (2 * nb) : ℚ) : ℝ) ≤ ((8 : ℚ) : ℝ) := by
    push_cast
    exact h2.trans (h3.le.trans h4)
  unfold pr
  exact_mod_cast h7
end ClauseBound.ParityChecks.Shape
