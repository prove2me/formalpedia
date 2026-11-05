-- Prove2me | solution 1 for CircuitLowerBound.Clause.litI_zeroCl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:52:27.050213+00:00
-- url     : https://prove2.me/submissions/8954647a-d8fa-42b4-a1a6-fe7f3aa8fbb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (ι : ℕ) : litI zeroCl ι = (0, 0, 0, 0, false) := by
  unfold litI zeroCl
  split_ifs <;> rfl
end CircuitLowerBound.Clause
