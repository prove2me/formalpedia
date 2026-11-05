-- Prove2me | solution 1 for ClauseBound.ParityChecks.logb_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:54:56.021867+00:00
-- url     : https://prove2.me/submissions/87d67b18-0d92-442d-aafb-aba90f9c052c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Theorems.Thm_ClauseBound_Rec_sum_choose_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Binom
namespace ClauseBound.ParityChecks
theorem _root_.solution {t μ μ' : ℕ} (h : μ ≤ μ') (h1 : 1 ≤ μ') :
    Real.logb 2 (t.choose μ) ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := by
  have hμ0 : (0 : ℝ) ≤ μ' := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (t.choose μ) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    exact mul_nonneg hμ0 (le_trans zero_le_one (le_max_left _ _))
  · have hpos : (0 : ℝ) < (t.choose μ : ℝ) := by exact_mod_cast h0
    rcases Nat.lt_or_ge t μ' with hlt | hge
    · have h2 : (t.choose μ : ℝ) ≤ 2 ^ μ' := by
        exact_mod_cast (Nat.choose_le_two_pow t μ).trans (Nat.pow_le_pow_right (by norm_num) hlt.le)
      calc Real.logb 2 (t.choose μ) ≤ Real.logb 2 ((2 : ℝ) ^ μ') := Real.logb_le_logb_of_le (by norm_num) hpos h2
        _ = μ' * 1 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        _ ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := mul_le_mul_of_nonneg_left (le_max_left _ _) hμ0
    · have h2 : (t.choose μ : ℝ) ≤ (3 * t / μ') ^ μ' := by
        refine le_trans ?_ (ClauseBound.Rec.sum_choose_le h1 hge)
        exact single_le_sum (f := fun ν => (t.choose ν : ℝ)) (fun _ _ => Nat.cast_nonneg _) (mem_range.2 (Nat.lt_succ_of_le h))
      calc Real.logb 2 (t.choose μ) ≤ Real.logb 2 ((3 * t / μ' : ℝ) ^ μ') := Real.logb_le_logb_of_le (by norm_num) hpos h2
        _ = μ' * Real.logb 2 (3 * t / μ') := by rw [Real.logb_pow]
        _ ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := mul_le_mul_of_nonneg_left (le_max_right _ _) hμ0
end ClauseBound.ParityChecks
