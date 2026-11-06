-- Prove2me | solution 1 for FixedWidthSteps.lg_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:15.766007+00:00
-- url     : https://prove2.me/submissions/a14e366b-c8cc-4d16-a7c7-c9972768a2d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_FixedWidthSteps_Small
import Theorems.Thm_Wrap_Arith_lg_add_four_facts


set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution {n : ℕ} (hn : 4 ≤ n) : 2 ≤ lg n ∧ 1 ≤ lg (lg n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have := Wrap.Arith.lg_add_four_facts m
  push_cast
  exact this
end FixedWidthSteps
