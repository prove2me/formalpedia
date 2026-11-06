-- Prove2me | solution 1 for ExplicitCost.bitsOut_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:08.053498+00:00
-- url     : https://prove2.me/submissions/23ead13a-79c0-4b38-afb7-187bb472bdf6

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
theorem _root_.solution (K g : ℕ) {u u' v v' : ℕ} (h1 : u ≤ u') (h2 : v ≤ v') : bitsOut K g u v ≤ bitsOut K g u' v' :=
  Nat.add_le_add (Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)) _)) (Nat.mul_le_mul_left _ h2)
end ExplicitCost
