-- Prove2me | solution 1 for ClauseBound.Group.Sample.avg_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:03.961276+00:00
-- url     : https://prove2.me/submissions/a1b7d062-f7b8-4282-a882-4a896bab87e6

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
import Theorems.Thm_ClauseBound_Rec_Tail_two_point_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
variable {ι : Type} [DecidableEq ι]
open ClauseBound.Group.Sample
omit [DecidableEq ι]
namespace ClauseBound.Group.Sample
theorem _root_.solution (s : Finset ι) (c : ι → ℝ) {R : ℝ} (hR : 0 < R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty) (θ : ℝ) :
    (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤ Real.exp (θ * ((∑ i ∈ s, c i) / #s) + (θ * R) ^ 2 / 8) := by
  have hN : (0 : ℝ) < #s := by exact_mod_cast card_pos.2 hs
  have h1 : ∀ i ∈ s, Real.exp (θ * c i) ≤ (1 - c i / R) + c i / R * Real.exp (θ * R) := by
    intro i hi
    obtain ⟨h0, hle⟩ := hc i hi
    have hb : 0 ≤ c i / R := by positivity
    have ha : 0 ≤ 1 - c i / R := by rw [sub_nonneg, div_le_one hR]; exact hle
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * R)) ha hb (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rwa [show c i / R * (θ * R) = θ * c i by field_simp] at h
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (∑ i ∈ s, c i) / #s / R := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i ∈ s, c i := sum_nonneg fun i hi => (hc i hi).1
  have hsumR : ∑ i ∈ s, c i ≤ #s * R := by
    calc ∑ i ∈ s, c i ≤ ∑ _i ∈ s, R := sum_le_sum fun i hi => (hc i hi).2
      _ = #s * R := by rw [sum_const, nsmul_eq_mul]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_div, div_le_one (by positivity)]; exact hsumR
  have h2 : (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤ (1 - p) + p * Real.exp (θ * R) := by
    rw [div_le_iff₀ hN]
    calc ∑ i ∈ s, Real.exp (θ * c i) ≤ ∑ i ∈ s, ((1 - c i / R) + c i / R * Real.exp (θ * R)) := sum_le_sum h1
      _ = #s - (∑ i ∈ s, c i) / R + (∑ i ∈ s, c i) / R * Real.exp (θ * R) := by
          rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← sum_div, ← sum_mul, ← sum_div]
      _ = ((1 - p) + p * Real.exp (θ * R)) * #s := by rw [hp]; field_simp
  have h3 := ClauseBound.Rec.Tail.two_point_le hp0 hp1 (θ * R)
  have h4 : (1 - p) + p * Real.exp (θ * R) =
      (p * Real.exp (θ * R * (1 - p)) + (1 - p) * Real.exp (θ * R * (0 - p))) * Real.exp (θ * R * p) := by
    have e1 : Real.exp (θ * R * (1 - p)) * Real.exp (θ * R * p) = Real.exp (θ * R) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (θ * R * (0 - p)) * Real.exp (θ * R * p) = 1 := by
      rw [← Real.exp_add, show θ * R * (0 - p) + θ * R * p = 0 by ring, Real.exp_zero]
    linear_combination (-p) * e1 - (1 - p) * e2
  have h5 : θ * ((∑ i ∈ s, c i) / #s) = θ * R * p := by rw [hp]; field_simp
  rw [h5, add_comm, Real.exp_add]
  refine h2.trans ?_
  rw [h4]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
end ClauseBound.Group.Sample
