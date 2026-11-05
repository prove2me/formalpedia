-- Prove2me | solution 1 for ClauseBound.Group.card_sample_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:31.821647+00:00
-- url     : https://prove2.me/submissions/c90061d4-1e15-4542-ab77-51874652c271

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
import Theorems.Thm_ClauseBound_Group_Sample_esymm_le
import Theorems.Thm_ClauseBound_Group_Sample_avg_exp_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
variable {ι : Type} [DecidableEq ι]
open Sample
namespace ClauseBound.Group
theorem _root_.solution (s : Finset ι) (c : ι → ℝ) {R t : ℝ} (hR : 0 < R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty)
    (n : ℕ) (ht : 0 ≤ t) :
    (#{S ∈ powersetCard n s | n * ((∑ i ∈ s, c i) / #s) + t * n * R ≤ ∑ i ∈ S, c i} : ℝ)
      ≤ Real.exp (-(2 * n * t ^ 2)) * ((#s).choose n : ℝ) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 4 * t / R := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (∑ i ∈ s, c i) / #s := ⟨_, rfl⟩
  rw [← hμ]
  have h1 : (#{S ∈ powersetCard n s | n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) * Real.exp (θ * (n * μ + t * n * R)) ≤
      ∑ S ∈ powersetCard n s, ∏ i ∈ S, Real.exp (θ * c i) := by
    calc (#{S ∈ powersetCard n s | n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) * Real.exp (θ * (n * μ + t * n * R))
        = ∑ _S ∈ powersetCard n s with n * μ + t * n * R ≤ ∑ i ∈ _S, c i, Real.exp (θ * (n * μ + t * n * R)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ powersetCard n s with n * μ + t * n * R ≤ ∑ i ∈ S, c i, ∏ i ∈ S, Real.exp (θ * c i) := by
          refine sum_le_sum fun S hS => ?_
          rw [← Real.exp_sum, ← mul_sum]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (mem_filter.1 hS).2 hθ0)
      _ ≤ ∑ S ∈ powersetCard n s, ∏ i ∈ S, Real.exp (θ * c i) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ => prod_nonneg fun i _ => (Real.exp_pos _).le
  have h2 := esymm_le s (fun i => Real.exp (θ * c i)) (fun i _ => (Real.exp_pos _).le) n
  have h3 : ((∑ i ∈ s, Real.exp (θ * c i)) / #s) ^ n ≤ Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) := by
    rw [Real.exp_nat_mul, hμ]
    exact pow_le_pow_left₀ (by positivity) (avg_exp_le s c hR hc hs θ) n
  have h4 : (#{S ∈ powersetCard n s | n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) * Real.exp (θ * (n * μ + t * n * R)) ≤
      ((#s).choose n : ℝ) * Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
  have h5 : Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) = Real.exp (-(2 * n * t ^ 2)) * Real.exp (θ * (n * μ + t * n * R)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hθ]
    field_simp
    ring
  rw [h5, ← mul_assoc] at h4
  have h6 := le_of_mul_le_mul_right h4 (Real.exp_pos _)
  linarith
end ClauseBound.Group
