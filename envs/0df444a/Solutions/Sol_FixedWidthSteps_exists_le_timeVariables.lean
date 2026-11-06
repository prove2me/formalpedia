-- Prove2me | solution 1 for FixedWidthSteps.exists_le_timeVariables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:24.426357+00:00
-- url     : https://prove2.me/submissions/6ff24c56-11b2-4409-a15c-8ec5b6a22c86

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
theorem _root_.solution (α : ℝ) {n : ℕ} (hn : 4 ≤ n) (N : ℕ) : ∃ C : ℕ, N ≤ timeVariables α C n := by
  have hE := expVariables_pos α hn
  obtain ⟨C, hC⟩ := exists_nat_ge ((N : ℝ) / expVariables α n)
  refine ⟨C, Nat.le_floor ?_⟩
  rw [div_le_iff₀ hE] at hC
  calc (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast Nat.lt_two_pow_self.le
    _ = (2 : ℝ) ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hC
end FixedWidthSteps
