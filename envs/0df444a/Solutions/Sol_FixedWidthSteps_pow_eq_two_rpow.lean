-- Prove2me | solution 1 for FixedWidthSteps.pow_eq_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:25.600195+00:00
-- url     : https://prove2.me/submissions/ae313e2b-7e9e-4e34-8523-e073e0e5177f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_FixedWidthSteps_Absorb

set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution {x : ℝ} (hx : 0 < x) (m : ℕ) : x ^ m = (2 : ℝ) ^ ((m : ℝ) * lg x) := by
  rw [mul_comm, Real.rpow_mul (by norm_num), show (2 : ℝ) ^ lg x = x from Real.rpow_logb (by norm_num) (by norm_num) hx, Real.rpow_natCast]
end FixedWidthSteps
