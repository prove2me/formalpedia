-- Prove2me | solution 1 for FixedWidthSteps.timeVariables_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:16:06.376997+00:00
-- url     : https://prove2.me/submissions/38a87280-81a0-4534-a005-2076aaaadfdb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_FixedWidthSteps_Small

set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution (α : ℝ) (C n : ℕ) : (timeVariables α C n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * expVariables α n) := Nat.floor_le (by positivity)
end FixedWidthSteps
