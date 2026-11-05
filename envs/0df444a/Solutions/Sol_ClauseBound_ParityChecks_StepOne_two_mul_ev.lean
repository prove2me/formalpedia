-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.two_mul_ev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:08.333534+00:00
-- url     : https://prove2.me/submissions/a5f2bc8d-46b6-4ded-ada8-1e95c64ce1ed

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
theorem _root_.solution (q : ℕ) : 2 * ev q = 1 + (-1) ^ q := by
  unfold ev
  by_cases h : Even q
  · rw [if_pos h, h.neg_one_pow]; norm_num
  · rw [if_neg h, (Nat.not_even_iff_odd.1 h).neg_one_pow]; norm_num
end ClauseBound.ParityChecks.StepOne
