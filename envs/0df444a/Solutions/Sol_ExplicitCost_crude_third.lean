-- Prove2me | solution 1 for ExplicitCost.crude_third
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:50.494224+00:00
-- url     : https://prove2.me/submissions/35f6b4cb-6a65-422f-b2e5-24456e2854ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CrudeBounds
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (g lam B s T E : ℕ) (hg : 3 ≤ g) (hl : lam ≤ s) (hB : B ≤ s) (hs : 2 ≤ s) (hT : T ≤ E) (hE : 1 ≤ E) :
    g * (g ^ 4 * lam + 1 + (g ^ 4 * lam + g ^ 2 * (g * B + g ^ 2 * T))) ≤ E * (g ^ 2 * s) ^ 5 := by
  have hg1 : 1 ≤ g := by omega
  have u1 : g ^ 5 * lam ≤ E * (g ^ 5 * s) := (Nat.mul_le_mul_left _ hl).trans (Nat.le_mul_of_pos_left _ hE)
  have u2 : g ≤ E * (g ^ 5 * s) :=
    ((Nat.le_self_pow (by norm_num) g).trans (Nat.le_mul_of_pos_right _ (by omega))).trans (Nat.le_mul_of_pos_left _ hE)
  have u3 : g ^ 4 * B ≤ E * (g ^ 5 * s) := (Nat.mul_le_mul (Nat.pow_le_pow_right hg1 (by norm_num)) hB).trans (Nat.le_mul_of_pos_left _ hE)
  have u4 : g ^ 5 * T ≤ E * (g ^ 5 * s) := by
    calc g ^ 5 * T ≤ g ^ 5 * s * E := Nat.mul_le_mul (Nat.le_mul_of_pos_right _ (by omega)) hT
      _ = E * (g ^ 5 * s) := Nat.mul_comm _ _
  have big : 5 ≤ g ^ 5 * s ^ 4 := by
    calc 5 ≤ 3 ^ 5 * 2 ^ 4 := by norm_num
      _ ≤ g ^ 5 * s ^ 4 := Nat.mul_le_mul (Nat.pow_le_pow_left hg 5) (Nat.pow_le_pow_left hs 4)
  calc g * (g ^ 4 * lam + 1 + (g ^ 4 * lam + g ^ 2 * (g * B + g ^ 2 * T))) = g ^ 5 * lam + g ^ 5 * lam + g + g ^ 4 * B + g ^ 5 * T := by ring
    _ ≤ 5 * (E * (g ^ 5 * s)) := by omega
    _ ≤ g ^ 5 * s ^ 4 * (E * (g ^ 5 * s)) := Nat.mul_le_mul_right _ big
    _ = E * (g ^ 2 * s) ^ 5 := by ring
end ExplicitCost
