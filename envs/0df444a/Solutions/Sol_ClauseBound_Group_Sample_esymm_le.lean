-- Prove2me | solution 1 for ClauseBound.Group.Sample.esymm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:43.297432+00:00
-- url     : https://prove2.me/submissions/44346ac7-e4e7-4a9f-b88d-79aa95d67f5a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Group_Sample
import Theorems.Thm_ClauseBound_Group_Sample_tangent_le
import Theorems.Thm_ClauseBound_Group_Sample_sum_powersetCard_insert

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
variable {ι : Type} [DecidableEq ι]
open ClauseBound.Group.Sample
namespace ClauseBound.Group.Sample
theorem _root_.solution (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∀ n : ℕ, ∑ S ∈ powersetCard n s, ∏ i ∈ S, x i ≤ ((#s).choose n : ℝ) * ((∑ i ∈ s, x i) / #s) ^ n := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rcases n with _ | n
    · simp
    · have h : powersetCard (n + 1) (∅ : Finset ι) = ∅ := powersetCard_eq_empty.2 (by simp)
      simp [h]
  | insert a s ha ih =>
    intro n
    rcases n with _ | k
    · simp
    have hxa : 0 ≤ x a := hx a (mem_insert_self a s)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have ih1 := ih hxs (k + 1)
    have ih0 := ih hxs k
    have hS0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    rw [sum_powersetCard_insert ha, card_insert_of_notMem ha, sum_insert ha]
    have hNu : (#s : ℝ) * ((∑ i ∈ s, x i) / #s) = ∑ i ∈ s, x i := by
      by_cases h0 : #s = 0
      · rw [card_eq_zero.1 h0]; simp
      · have : (#s : ℝ) ≠ 0 := by exact_mod_cast h0
        field_simp
    have hNw : ((#s : ℝ) + 1) * ((x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1)) = x a + ∑ i ∈ s, x i := by
      have : (#s : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hu : 0 ≤ (∑ i ∈ s, x i) / #s := by positivity
    have hw : 0 ≤ (x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1) := by positivity
    have h1 : ((#s : ℝ) + 1) * ((#s).choose k : ℝ) = ((#s + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (#s) k
    have h2 : ((#s + 1).choose (k + 1) : ℝ) = ((#s).choose k : ℝ) + ((#s).choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (#s) k
    push_cast
    generalize (∑ i ∈ s, x i) / #s = u at *
    generalize (x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1) = w at *
    have hv : x a = ((#s : ℝ) + 1) * w - #s * u := by linarith
    have ht := tangent_le u w hu hw k
    calc ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i + x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i
        ≤ ((#s).choose (k + 1) : ℝ) * u ^ (k + 1) + x a * (((#s).choose k : ℝ) * u ^ k) :=
          add_le_add ih1 (mul_le_mul_of_nonneg_left ih0 hxa)
      _ = ((#s + 1).choose (k + 1) : ℝ) * (((k : ℝ) + 1) * w * u ^ k - k * u ^ (k + 1)) := by
          rw [hv]
          linear_combination (w * u ^ k - u ^ (k + 1)) * h1 - u ^ (k + 1) * h2
      _ ≤ ((#s + 1).choose (k + 1) : ℝ) * w ^ (k + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end ClauseBound.Group.Sample
