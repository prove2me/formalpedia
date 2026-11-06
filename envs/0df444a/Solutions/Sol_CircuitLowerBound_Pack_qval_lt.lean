-- Prove2me | solution 1 for CircuitLowerBound.Pack.qval_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:12.70522+00:00
-- url     : https://prove2.me/submissions/5db9731b-6e2d-444c-b757-a7adc298fefe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
namespace CircuitLowerBound.Pack
theorem _root_.solution {Q P q : ℕ} (hq : q < 2 ^ Q) (hP : P < 2 ^ Q) (mode : ℕ) : qval P q mode < 2 ^ Q := by
  unfold qval
  split_ifs <;> omega
end CircuitLowerBound.Pack
