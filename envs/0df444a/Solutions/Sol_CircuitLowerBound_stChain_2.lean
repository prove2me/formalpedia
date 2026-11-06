-- Prove2me | solution 2 for CircuitLowerBound.stChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:05.797747+00:00
-- url     : https://prove2.me/submissions/92a1a772-69b1-4182-bd8a-b725941fa2f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_nu_pow_mul

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open SmallFacts
namespace CircuitLowerBound
theorem _root_.solution : StChain := fun a s => by
  have h := nu_pow_mul a s
  refine ⟨h, ?_⟩
  rw [pos, h, Nat.mul_div_cancel_left _ (by positivity)]
  omega
end CircuitLowerBound
