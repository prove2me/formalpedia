-- Prove2me | solution 1 for ExplicitCost.crude_plain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:33:12.367221+00:00
-- url     : https://prove2.me/submissions/fc5dc450-46fb-4e54-89f5-f0801f6099a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CrudeBounds
import Theorems.Thm_ExplicitCost_crude_first
import Theorems.Thm_ExplicitCost_crude_second
import Theorems.Thm_ExplicitCost_crude_third
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (c K g lam B L : ℕ) (hK : 3 ≤ K) (hKg : K ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hL : L ≤ g ^ 4 * lam + 1) :
    bitsOut K g (g ^ 3 * lam) (bitsOne c g lam B) ≤ g ^ 4 * lam + g ^ 2 * bitsOne c g lam B ∧
    g * (g ^ 3 * lam + bitsOne c g lam B) ≤ Xi g lam B ^ (c + 4) ∧
    K * (L + bitsOut K g (g ^ 3 * lam) (bitsOne c g lam B)) ≤ Xi g lam B ^ (c + 5) := by
  have hg : 3 ≤ g := hK.trans hKg
  have h1 := crude_first K g lam (bitsOne c g lam B) hK hg hlam
  have hX : 2 * lam ≤ g ^ 2 * (lam + B) := Nat.mul_le_mul ((by norm_num : 2 ≤ 3 ^ 2).trans (Nat.pow_le_pow_left hg 2)) (Nat.le_add_right _ _)
  have hT : (2 * lam) ^ c ≤ (g ^ 2 * (lam + B)) ^ c := Nat.pow_le_pow_left hX c
  have hE : 1 ≤ (g ^ 2 * (lam + B)) ^ c := Nat.one_le_pow _ _ (by omega)
  refine ⟨h1, ?_, ?_⟩
  · unfold Xi bitsOne
    rw [pow_add]
    exact crude_second g lam B (lam + B) _ _ hg (Nat.le_add_right _ _) (Nat.le_add_left _ _) (by omega) hT hE
  · refine (Nat.mul_le_mul hKg (Nat.add_le_add hL h1)).trans ?_
    unfold Xi bitsOne
    rw [pow_add]
    exact crude_third g lam B (lam + B) _ _ hg (Nat.le_add_right _ _) (Nat.le_add_left _ _) (by omega) hT hE
end ExplicitCost
