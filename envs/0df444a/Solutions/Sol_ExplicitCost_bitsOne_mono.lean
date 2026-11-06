-- Prove2me | solution 1 for ExplicitCost.bitsOne_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:06.810352+00:00
-- url     : https://prove2.me/submissions/e71d8b78-3805-4f35-8b4f-14f50f1a7762

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
theorem _root_.solution (c g : ℕ) {u u' v v' : ℕ} (h1 : u ≤ u') (h2 : v ≤ v') : bitsOne c g u v ≤ bitsOne c g u' v' :=
  Nat.add_le_add (Nat.mul_le_mul_left _ h2) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h1) _))
end ExplicitCost
