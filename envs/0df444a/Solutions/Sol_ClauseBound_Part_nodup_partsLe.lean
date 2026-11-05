-- Prove2me | solution 1 for ClauseBound.Part.nodup_partsLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:50.750121+00:00
-- url     : https://prove2.me/submissions/fdcdb667-1daa-4980-ae60-81945dd7e467

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
import Theorems.Thm_ClauseBound_Part_mem_partsLe

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution (E k : ℕ) : (partsLe E k).Nodup := by
  induction E using Nat.strong_induction_on generalizing k with
  | _ E ihE =>
    induction k with
    | zero =>
      rw [partsLe_zero_right]
      split_ifs
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    | succ k ihk =>
      rw [partsLe_succ]
      refine List.nodup_append.2 ⟨ihk, ?_, ?_⟩
      · split_ifs with hkE
        · exact (ihE (E - (k + 1)) (by omega) (k + 1)).map (List.cons_injective)
        · exact List.nodup_nil
      · intro A hA B hB hAB
        subst hAB
        split_ifs at hB
        · obtain ⟨L', _, rfl⟩ := List.mem_map.1 hB
          have := (((mem_partsLe _ _ _).1 hA).2.1 (k + 1) List.mem_cons_self).2
          omega
        · exact absurd hB List.not_mem_nil
end ClauseBound.Part
