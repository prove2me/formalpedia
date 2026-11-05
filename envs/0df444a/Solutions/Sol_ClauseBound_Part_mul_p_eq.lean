-- Prove2me | solution 1 for ClauseBound.Part.mul_p_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:30.564186+00:00
-- url     : https://prove2.me/submissions/96557411-4a0a-4487-8519-58fd624ddfa7

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
import Theorems.Thm_ClauseBound_Part_card_count_ge

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution (E : ℕ) : E * p E = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), v * p (E - k * v) := by
  have h1 : ∀ π : Nat.Partition E, ∑ v ∈ Icc 1 E, π.parts.count v * v = E := by
    intro π
    have hsub : π.parts.toFinset ⊆ Icc 1 E := fun v hv =>
      mem_Icc.2 ⟨π.parts_pos (Multiset.mem_toFinset.1 hv), π.le_of_mem_parts (Multiset.mem_toFinset.1 hv)⟩
    have h := Finset.sum_multiset_count_of_subset π.parts (Icc 1 E) hsub
    rw [π.parts_sum] at h
    simpa only [smul_eq_mul] using h.symm
  have h2 : ∀ π : Nat.Partition E, ∀ v ∈ Icc 1 E, #{k ∈ Icc 1 (E / v) | k ≤ π.parts.count v} = π.parts.count v := by
    intro π v hv
    have hle : π.parts.count v * v ≤ E :=
      (single_le_sum (f := fun v => π.parts.count v * v) (fun _ _ => Nat.zero_le _) hv).trans (h1 π).le
    have hle' : π.parts.count v ≤ E / v := (Nat.le_div_iff_mul_le (mem_Icc.1 hv).1).2 hle
    have heq : {k ∈ Icc 1 (E / v) | k ≤ π.parts.count v} = Icc 1 (π.parts.count v) := by
      ext k
      simp only [mem_filter, mem_Icc]
      omega
    rw [heq, Nat.card_Icc, Nat.add_sub_cancel]
  calc E * p E = ∑ _π : Nat.Partition E, E := by rw [sum_const, card_univ, smul_eq_mul, mul_comm, p]
    _ = ∑ π : Nat.Partition E, ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), if k ≤ π.parts.count v then v else 0 := by
        refine sum_congr rfl fun π _ => (h1 π).symm.trans (sum_congr rfl fun v hv => ?_)
        rw [← sum_filter, sum_const, smul_eq_mul, h2 π v hv]
    _ = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), ∑ π : Nat.Partition E, if k ≤ π.parts.count v then v else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun v _ => sum_comm
    _ = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), v * p (E - k * v) := by
        refine sum_congr rfl fun v hv => sum_congr rfl fun k hk => ?_
        have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
        rw [← sum_filter, sum_const, smul_eq_mul, card_count_ge hv1 ((Nat.le_div_iff_mul_le hv1).1 (mem_Icc.1 hk).2), mul_comm]
end ClauseBound.Part
