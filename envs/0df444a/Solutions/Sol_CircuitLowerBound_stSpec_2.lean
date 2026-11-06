-- Prove2me | solution 2 for CircuitLowerBound.stSpec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:32:01.582936+00:00
-- url     : https://prove2.me/submissions/01b3e16b-b7ae-4e36-a8b7-a1d78b68ceb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Complete
import Theorems.Thm_CircuitLowerBound_Tab_spec_of_acc
import Theorems.Thm_CircuitLowerBound_Tab_acc_of_spec


set_option autoImplicit false
section
section
open CircuitLowerBound
open Tab
namespace CircuitLowerBound
theorem _root_.solution : StSpec := fun _ _ _ _ _ hP => ⟨fun ⟨_, h⟩ => acc_of_spec hP h, fun h => spec_of_acc _ h⟩
end CircuitLowerBound
