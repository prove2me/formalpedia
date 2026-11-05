-- Prove2me | solution 1 for ClauseBound.Part.ListP.length_partsLe_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:59.414191+00:00
-- url     : https://prove2.me/submissions/50438f18-c221-43b9-aacb-2a2b83160123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_ListP
import Theorems.Thm_ClauseBound_Part_partsLe_zero_right
import Theorems.Thm_ClauseBound_Part_partsLe_succ
import Theorems.Thm_ClauseBound_Part_partsLe_of_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.ListP
namespace ClauseBound.Part.ListP
theorem _root_.solution (E k : ℕ) : (partsLe E k).length ≤ 2 ^ E ∧ (1 ≤ E → (partsLe E k).length + 2 ^ (E - k) ≤ 2 ^ E) := by
  induction E using Nat.strong_induction_on generalizing k with
  | _ E ihE =>
    have key : 1 ≤ E → (partsLe E k).length + 2 ^ (E - k) ≤ 2 ^ E := by
      intro hE
      induction k with
      | zero => rw [partsLe_zero_right, if_neg (by omega)]; simp
      | succ k ihk =>
        rw [partsLe_succ, List.length_append]
        split_ifs with hkE
        · have h1 := (ihE (E - (k + 1)) (by omega) (k + 1)).1
          have h2 : 2 ^ (E - k) = 2 * 2 ^ (E - (k + 1)) := by
            rw [show E - k = (E - (k + 1)) + 1 by omega, pow_succ]; ring
          rw [List.length_map]
          omega
        · rw [show E - (k + 1) = E - k by omega]
          simpa using ihk
    refine ⟨?_, key⟩
    rcases Nat.eq_zero_or_pos E with rfl | hE
    · rw [partsLe_of_le (Nat.zero_le k), partsOf, partsLe_zero_right]
      simp
    · exact (Nat.le_add_right _ _).trans (key hE)
end ClauseBound.Part.ListP
