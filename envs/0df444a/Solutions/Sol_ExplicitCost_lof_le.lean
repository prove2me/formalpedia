-- Prove2me | solution 1 for ExplicitCost.lof_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:45.155419+00:00
-- url     : https://prove2.me/submissions/d82620aa-2739-4c17-9274-99b70d99799c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {K g P U : ℕ} {ζ : ℝ} (hK : 1 ≤ K) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (hU : U ≤ g * P) : AppRunningTime.Lof K g ζ P U ≤ 3 * (g * P) := by
  unfold AppRunningTime.Lof
  refine Nat.ceil_le.2 ?_
  have hK' : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hK)
  have hU' : (U : ℝ) ≤ (g : ℝ) * P := by exact_mod_cast hU
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hgP : (0 : ℝ) ≤ (g : ℝ) * P := by positivity
  have h2 : 2 * ζ * g * P = 2 * (ζ * ((g : ℝ) * P)) := by ring
  have h3 : ζ * ((g : ℝ) * P) ≤ 1 * ((g : ℝ) * P) := mul_le_mul_of_nonneg_right h1 hgP
  have h4 : 0 ≤ ζ * ((g : ℝ) * P) := mul_nonneg h0 hgP
  rw [h2]
  calc ((U : ℝ) + 2 * (ζ * ((g : ℝ) * P))) / (K : ℝ) ^ 2 ≤ (U : ℝ) + 2 * (ζ * ((g : ℝ) * P)) := div_le_self (by linarith) hK'
    _ ≤ 3 * ((g : ℝ) * P) := by linarith
    _ = ((3 * (g * P) : ℕ) : ℝ) := by push_cast; ring
end ExplicitCost
