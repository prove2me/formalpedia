-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.sum_powerset_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:12.999865+00:00
-- url     : https://prove2.me/submissions/8ae55cc0-a241-4862-843e-df7b1c5b18da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_neg_one_pow_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {E : Type} (A : Finset E) : ∑ s ∈ A.powerset, (-2 : ℤ) ^ #s = (-1) ^ #A := by
  rw [sum_powerset_apply_card (fun i => (-2 : ℤ) ^ i), neg_one_pow_eq]
  exact sum_congr rfl fun i _ => by rw [nsmul_eq_mul, mul_comm]
end ClauseBound.ParityChecks.StepOne
