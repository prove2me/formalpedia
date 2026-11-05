-- Prove2me | solution 1 for CircuitLowerBound.Acc.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:32:28.478427+00:00
-- url     : https://prove2.me/submissions/e0946076-4d65-4abd-abdb-e3b8c503e100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
namespace CircuitLowerBound
namespace Acc
theorem _root_.solution {N : TM2ComputableAux Bool Bool} {P T T' : ℕ} (h : Acc N P T) (hT : T ≤ T') : Acc N P T' := by
  obtain ⟨y, ⟨h⟩⟩ := h
  exact ⟨y, ⟨⟨h.toEvalsTo, h.steps_le_m.trans hT⟩⟩⟩
end Acc
end CircuitLowerBound
