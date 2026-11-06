-- Prove2me | solution 3 for CircuitLowerBound.Inf.Ext.congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:27.34107+00:00
-- url     : https://prove2.me/submissions/183983cd-e0a4-4165-8ee3-c6c827b0eb10

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP
namespace CircuitLowerBound.Inf
namespace Ext
theorem _root_.solution {n : ℕ} {g g' : List Bool → Bool} (h : Ext n g) (e : ∀ x : List Bool, x.length = n → g x = g' x) : Ext n g' := fun C₀ => by
  obtain ⟨D, w, hw, hD⟩ := h C₀
  exact ⟨D, w, hw, fun x hx => (hD x hx).trans (e x hx)⟩
end Ext
end CircuitLowerBound.Inf
