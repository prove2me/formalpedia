-- Prove2me | solution 1 for ExplicitCost.xi_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:21:25.914758+00:00
-- url     : https://prove2.me/submissions/9179c95e-6828-4818-bab0-740c79670da3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {g lam B : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) :
    8 ≤ Xi g lam B ∧ g ≤ Xi g lam B ∧ 2 * (g * g) ≤ Xi g lam B ∧ 2 * lam ≤ Xi g lam B ∧ B ≤ Xi g lam B ∧ g * (g * g) * lam ≤ Xi g lam B * Xi g lam B ∧ B * g ≤ Xi g lam B * Xi g lam B := by
  have h4 : 4 ≤ g * g := Nat.mul_le_mul hg hg
  have e : Xi g lam B = g * g * (lam + B) := by unfold Xi; ring
  have h1 : g * g * 2 ≤ g * g * (lam + B) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 4 * (lam + B) ≤ g * g * (lam + B) := Nat.mul_le_mul_right _ h4
  have h3 : g ≤ g * g := Nat.le_mul_of_pos_left _ (by omega)
  rw [e]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · calc g * (g * g) * lam ≤ (g * g) * (g * g) * ((lam + B) * (lam + B)) := by
          refine Nat.mul_le_mul (Nat.mul_le_mul_right _ h3) ?_
          exact (Nat.le_add_right lam B).trans (Nat.le_mul_of_pos_left _ (by omega))
      _ = g * g * (lam + B) * (g * g * (lam + B)) := by ring
  · calc B * g ≤ (g * g * (lam + B)) * (g * g * (lam + B)) := Nat.mul_le_mul (by omega) (by omega)
end ExplicitCost
