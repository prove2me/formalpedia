-- Prove2me | solution 1 for CircuitLowerBound.Clause.gval_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:49:35.002249+00:00
-- url     : https://prove2.me/submissions/0448ea7d-b1a4-45ca-b628-1adc2b4d5ea6

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
theorem _root_.solution (v : ℕ → Bool) (c : Bool) (o₁ o₂ : B4) (i j : ℕ) :
    gval v ((if c then o₁ else o₂), i, j) = if c then gval v (o₁, i, j) else gval v (o₂, i, j) := by
  cases c <;> rfl
end CircuitLowerBound.Clause
