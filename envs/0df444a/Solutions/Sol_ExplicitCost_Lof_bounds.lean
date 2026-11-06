-- Prove2me | solution 1 for ExplicitCost.Lof_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:26.237859+00:00
-- url     : https://prove2.me/submissions/77164fe8-cdef-4de3-83c0-d8367df1dca0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {K g P U b : ℕ} (hK : 2 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hb : 1 ≤ b) (hU : U ≤ g * P) : 1 ≤ AppRunningTime.Lof K g ((1 : ℝ) / b) P U ∧ AppRunningTime.Lof K g ((1 : ℝ) / b) P U ≤ g * P := by
  unfold AppRunningTime.Lof
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg U
  have hζ1 : (1 : ℝ) / b ≤ 1 := (div_le_one hb0).2 hbr
  have hζ0 : (0 : ℝ) < 1 / b := by positivity
  constructor
  · exact Nat.ceil_pos.2 (div_pos (by positivity) (by positivity))
  · refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have hUr : (U : ℝ) ≤ g * P := by exact_mod_cast hU
    have h4 : (4 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hgP : (0 : ℝ) < (g : ℝ) * P := by positivity
    have h2 : 2 * (1 / (b : ℝ)) * g * P ≤ 2 * ((g : ℝ) * P) := by
      have : 1 / (b : ℝ) * ((g : ℝ) * P) ≤ 1 * ((g : ℝ) * P) := mul_le_mul_of_nonneg_right hζ1 hgP.le
      nlinarith
    nlinarith
end ExplicitCost
