-- Prove2me | solution 1 for ExplicitCost.top_inBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:34.165946+00:00
-- url     : https://prove2.me/submissions/2209537e-3b11-4bd1-9f84-efb427407445

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_CliqueReads
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndCounted
import Theorems.Thm_ExplicitCost_cLev_top
import Theorems.Thm_ExplicitCost_cLam_top
import Theorems.Thm_ExplicitCost_cB_top

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) (c x₀ l lam B : ℕ) : InBounds ρ c x₀ l lam B (top l lam B) := by
  unfold InBounds lamAt bitsAt
  rw [cLev_top, cLam_top, cB_top, Nat.sub_self]
  exact ⟨le_rfl, le_rfl, le_rfl⟩
end ExplicitCost
