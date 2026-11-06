-- Prove2me | solution 1 for ExplicitCost.lamAt_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:53.169401+00:00
-- url     : https://prove2.me/submissions/cf12c5af-6bae-4bd0-a47e-65c4f267a1e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) (c x₀ lam B : ℕ) {i : ℕ} (hi : i ≤ l) : lamAt ρ c x₀ l lam B i ≤ lamMax ρ c x₀ l lam B :=
  Finset.le_sup (f := fun j => lamAt ρ c x₀ l lam B j) (Finset.mem_range.2 (by omega))
end ExplicitCost
