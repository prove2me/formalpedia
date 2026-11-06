-- Prove2me | solution 1 for FixedWidthSteps.two_rpow_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:10:07.929589+00:00
-- url     : https://prove2.me/submissions/d8566bb2-7f19-4a1f-a7af-7dd021e70318

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
theorem _root_.solution {a b : ℕ} (h : a ≤ b) {E : ℝ} (hE : 0 ≤ E) : (2 : ℝ) ^ ((a : ℝ) * E) ≤ (2 : ℝ) ^ ((b : ℝ) * E) :=
  Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) hE)
end FixedWidthSteps
