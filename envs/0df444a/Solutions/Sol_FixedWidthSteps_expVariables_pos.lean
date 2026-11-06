-- Prove2me | solution 1 for FixedWidthSteps.expVariables_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:25:19.759644+00:00
-- url     : https://prove2.me/submissions/94477335-83cb-4d7a-8e6d-29980575cc6f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_FixedWidthSteps_Small
import Theorems.Thm_FixedWidthSteps_lg_facts

set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution (α : ℝ) {n : ℕ} (hn : 4 ≤ n) : 0 < expVariables α n := by
  obtain ⟨h1, h2⟩ := lg_facts hn
  have h3 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h4 : 0 < lg n ^ α := Real.rpow_pos_of_pos (by linarith) _
  exact div_pos (mul_pos h3 (by linarith)) h4
end FixedWidthSteps
