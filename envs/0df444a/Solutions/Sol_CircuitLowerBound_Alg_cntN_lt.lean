-- Prove2me | solution 1 for CircuitLowerBound.Alg.cntN_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:50:13.522928+00:00
-- url     : https://prove2.me/submissions/c9e492c1-2d1d-469a-b31b-5b5d2ad32dbc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}
namespace CircuitLowerBound.Alg
theorem _root_.solution (N : ℕ) (ψ : Cnf) : CountKSat.cntN N ψ < 2 ^ (N + 1) := by
  unfold CountKSat.cntN
  refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self N)
end CircuitLowerBound.Alg
