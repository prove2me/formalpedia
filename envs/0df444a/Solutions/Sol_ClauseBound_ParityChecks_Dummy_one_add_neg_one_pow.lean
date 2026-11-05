-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.one_add_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:00.608689+00:00
-- url     : https://prove2.me/submissions/ff572fb0-1837-429e-86d4-0bf93f05c846

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution (q : ℕ) : (-1 : ℤ) ^ q + 1 = 2 * ev q := by
  unfold ev
  rcases Nat.even_or_odd q with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.2 h)]; norm_num
end ClauseBound.ParityChecks.Dummy
