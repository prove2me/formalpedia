-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.neg_one_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:02.467142+00:00
-- url     : https://prove2.me/submissions/40135476-f070-4f47-a495-4e2910316074

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution (q : ℕ) : (-1 : ℤ) ^ q = ∑ i ∈ range (q + 1), (-2 : ℤ) ^ i * q.choose i := by
  have h := add_pow (-2 : ℤ) 1 q
  rw [show (-2 : ℤ) + 1 = -1 by norm_num] at h
  rw [h]
  exact sum_congr rfl fun i _ => by rw [one_pow, mul_one]
end ClauseBound.ParityChecks.StepOne
