-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:56.498092+00:00
-- url     : https://prove2.me/submissions/7fb1930c-94f6-4dcf-9234-446843175161

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_mul_sig
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_mul_ev
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_neg_one_pow_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution (q : ℕ) : ev q = ∑ i ∈ range (q + 1), sig i * q.choose i := by
  have h1 : ∑ i ∈ range (q + 1), (if i = 0 then (1 : ℤ) else 0) * q.choose i = 1 := by
    rw [sum_eq_single 0 (fun i _ hi => by rw [if_neg hi, zero_mul]) (fun h => absurd (mem_range.2 (Nat.succ_pos q)) h)]
    simp
  have h2 : 2 * ∑ i ∈ range (q + 1), sig i * q.choose i = 2 * ev q := by
    rw [two_mul_ev, neg_one_pow_eq, ← h1, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, two_mul_sig]
    ring
  linarith
end ClauseBound.ParityChecks.StepOne
