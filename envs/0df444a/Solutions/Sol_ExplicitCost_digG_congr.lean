-- Prove2me | solution 1 for ExplicitCost.digG_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:14:24.264239+00:00
-- url     : https://prove2.me/submissions/67ad3326-b2c6-4da7-be2b-6af96f388256

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {P P' : PiecesF} {h ℓ : ℕ}
namespace ExplicitCost
theorem _root_.solution (hc : P.cnt h ℓ = P'.cnt h ℓ) (d : ℕ) (tr : Bool) (y q κ : ℕ) : digG P d tr h ℓ y q κ = digG P' d tr h ℓ y q κ := by
  unfold digG
  rw [hc]
end ExplicitCost
