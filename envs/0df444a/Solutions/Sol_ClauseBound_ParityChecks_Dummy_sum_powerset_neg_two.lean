-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.sum_powerset_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:49.752371+00:00
-- url     : https://prove2.me/submissions/6eab3f84-d127-4caa-b889-4a953217a8c8

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
theorem _root_.solution {α : Type} (T : Finset α) : ∑ S ∈ T.powerset, (-2 : ℤ) ^ #S = (-1) ^ #T := by
  have h := sum_pow_mul_eq_add_pow (-2 : ℤ) 1 T
  simp only [one_pow, mul_one] at h
  rw [h]
  norm_num
end ClauseBound.ParityChecks.Dummy
