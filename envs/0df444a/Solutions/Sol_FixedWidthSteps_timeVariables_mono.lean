-- Prove2me | solution 1 for FixedWidthSteps.timeVariables_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:18:19.839138+00:00
-- url     : https://prove2.me/submissions/63eff145-ad68-4bc0-ae97-14e36c4e73be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_FixedWidthSteps_Small
import Theorems.Thm_FixedWidthSteps_expVariables_pos

set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution (α : ℝ) {C C' n : ℕ} (hn : 4 ≤ n) (h : C ≤ C') : timeVariables α C n ≤ timeVariables α C' n :=
  Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) (expVariables_pos α hn).le))
end FixedWidthSteps
