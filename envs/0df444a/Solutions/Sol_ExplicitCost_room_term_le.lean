-- Prove2me | solution 1 for ExplicitCost.room_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:18.404861+00:00
-- url     : https://prove2.me/submissions/7a1be0b9-e1da-4535-909d-ce6b32988081

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) (c x₀ lam B : ℕ) {C C' i u v : ℕ} (hC : C' ≤ C) (hi : i ≤ l) (h1 : 1 ≤ u) (hu : u ≤ lamAt ρ c x₀ l lam B i) (hv : v ≤ bitsAt ρ c x₀ l lam B i) : (Levels.Gen.K x₀ i * (u + v)) ^ C' ≤ roomAll C ρ c x₀ l lam B := by
  have hK := K_pos x₀ i
  have hb : 1 ≤ Levels.Gen.K x₀ i * (lamAt ρ c x₀ l lam B i + bitsAt ρ c x₀ l lam B i) := Nat.mul_pos hK (by omega)
  calc (Levels.Gen.K x₀ i * (u + v)) ^ C' ≤ (Levels.Gen.K x₀ i * (lamAt ρ c x₀ l lam B i + bitsAt ρ c x₀ l lam B i)) ^ C' := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.add_le_add hu hv)) _
    _ ≤ (Levels.Gen.K x₀ i * (lamAt ρ c x₀ l lam B i + bitsAt ρ c x₀ l lam B i)) ^ C := Nat.pow_le_pow_right hb hC
    _ ≤ roomAll C ρ c x₀ l lam B := Finset.single_le_sum (f := fun j => (Levels.Gen.K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
end ExplicitCost
