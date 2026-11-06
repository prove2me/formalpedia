-- Prove2me | solution 1 for ExplicitCost.crude_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:34.705632+00:00
-- url     : https://prove2.me/submissions/c4817f0c-8638-47ff-9e75-0d8ed56d19e8

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
    g * (g ^ 3 * lam + (g * B + g ^ 2 * T)) ≤ E * (g ^ 2 * s) ^ 4 := by
  have hg1 : 1 ≤ g := by omega
  have t1 : g ^ 4 * lam ≤ E * (g ^ 4 * s) := (Nat.mul_le_mul_left _ hl).trans (Nat.le_mul_of_pos_left _ hE)
  have t2 : g ^ 2 * B ≤ E * (g ^ 4 * s) := (Nat.mul_le_mul (Nat.pow_le_pow_right hg1 (by norm_num)) hB).trans (Nat.le_mul_of_pos_left _ hE)
  have t3 : g ^ 3 * T ≤ E * (g ^ 4 * s) := by
    calc g ^ 3 * T ≤ g ^ 4 * s * E := Nat.mul_le_mul ((Nat.pow_le_pow_right hg1 (by norm_num)).trans (Nat.le_mul_of_pos_right _ (by omega))) hT
      _ = E * (g ^ 4 * s) := Nat.mul_comm _ _
  have big : 3 ≤ g ^ 4 * s ^ 3 := by
    calc 3 ≤ 3 ^ 4 * 2 ^ 3 := by norm_num
      _ ≤ g ^ 4 * s ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hg 4) (Nat.pow_le_pow_left hs 3)
  calc g * (g ^ 3 * lam + (g * B + g ^ 2 * T)) = g ^ 4 * lam + g ^ 2 * B + g ^ 3 * T := by ring
    _ ≤ 3 * (E * (g ^ 4 * s)) := by omega
    _ ≤ g ^ 4 * s ^ 3 * (E * (g ^ 4 * s)) := Nat.mul_le_mul_right _ big
    _ = E * (g ^ 2 * s) ^ 4 := by ring
end ExplicitCost
