-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.choose_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:09.108273+00:00
-- url     : https://prove2.me/submissions/d7f3acb3-63d1-4070-96ed-3771d05369a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_Rec_sum_choose_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution {N k j w : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ N) (hj : j ≤ k) (hw : 3 * N ≤ k * 2 ^ w) : N.choose j ≤ 2 ^ (w * k) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast h1
  have h3 := ClauseBound.Rec.sum_choose_le h1 h2
  have h4 : (N.choose j : ℝ) ≤ ∑ ν ∈ range (k + 1), (N.choose ν : ℝ) :=
    single_le_sum (f := fun ν => (N.choose ν : ℝ)) (fun _ _ => by positivity) (mem_range.2 (by omega))
  have h5 : (3 * (N : ℝ) / k) ≤ 2 ^ w := by
    rw [div_le_iff₀ hk]
    have : ((3 * N : ℕ) : ℝ) ≤ ((k * 2 ^ w : ℕ) : ℝ) := by exact_mod_cast hw
    push_cast at this
    linarith
  have h6 : (3 * (N : ℝ) / k) ^ k ≤ (2 ^ w) ^ k := pow_le_pow_left₀ (by positivity) h5 k
  have h7 : (N.choose j : ℝ) ≤ ((2 ^ (w * k) : ℕ) : ℝ) := by
    push_cast
    rw [pow_mul]
    linarith
  exact_mod_cast h7
end ClauseBound.ParityChecks.Params
