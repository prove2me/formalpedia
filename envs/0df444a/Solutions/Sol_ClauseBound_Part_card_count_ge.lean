-- Prove2me | solution 1 for ClauseBound.Part.card_count_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:34.185194+00:00
-- url     : https://prove2.me/submissions/5853ba9b-236c-4c96-89be-2ac0e5a64d51

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

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution {E v k : ℕ} (hv : 1 ≤ v) (h : k * v ≤ E) :
    #{π : Nat.Partition E | k ≤ π.parts.count v} = p (E - k * v) := by
  have hsum : (Multiset.replicate k v).sum = k * v := by rw [Multiset.sum_replicate, smul_eq_mul]
  rw [p, ← card_univ]
  refine card_bij'
    (fun π hπ => ⟨π.parts - Multiset.replicate k v, fun hi => π.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi), ?_⟩)
    (fun σ _ => ⟨σ.parts + Multiset.replicate k v, fun hi => ?_, ?_⟩) (fun _ _ => mem_univ _) (fun σ _ => ?_) (fun π hπ => ?_) (fun σ _ => ?_)
  · have hle : Multiset.replicate k v ≤ π.parts := Multiset.le_count_iff_replicate_le.1 (mem_filter.1 hπ).2
    have h1 := congrArg Multiset.sum (Multiset.sub_add_cancel hle)
    rw [Multiset.sum_add, hsum, π.parts_sum] at h1
    omega
  · rcases Multiset.mem_add.1 hi with hi | hi
    · exact σ.parts_pos hi
    · rw [Multiset.eq_of_mem_replicate hi]
      exact hv
  · rw [Multiset.sum_add, hsum, σ.parts_sum]
    omega
  · simp
  · exact Nat.Partition.ext (Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.1 (mem_filter.1 hπ).2))
  · exact Nat.Partition.ext Multiset.add_sub_cancel_right
end ClauseBound.Part
