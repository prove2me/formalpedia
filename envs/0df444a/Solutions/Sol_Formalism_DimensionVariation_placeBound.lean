-- Prove2me | solution 1 for Formalism.DimensionVariation.placeBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:04.951775+00:00
-- url     : https://prove2.me/submissions/67423197-5b39-42e3-990a-23b83554e6fa

import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialSandwich
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset MeasureTheory
open scoped ComplexConjugate Real
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
private theorem rpow_mul_exp_neg_sq_le_exp_ph_mul_exp_log (ν s a : ℝ) (hν : 0 ≤ ν) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hνa : ν = 0 ∨ 0 < a) :
    s ^ ν * Real.exp (-(a * s ^ 2) / 2) ≤ Real.exp (ph ν / 2) * Real.exp (-(ν * Real.log a) / 2) := by
  rcases hν.eq_or_lt with h0 | hν
  · subst h0
    have : Real.exp (-(a * s ^ 2) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg ha (sq_nonneg s)])
    simpa [ph] using this
  · have ha' : 0 < a := hνa.resolve_left hν.ne'
    rcases hs.eq_or_lt with hs0 | hs
    · subst hs0
      rw [Real.zero_rpow hν.ne', zero_mul]; positivity
    · rw [Real.rpow_def_of_pos hs, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hy := Real.log_le_sub_one_of_pos (show 0 < a * s ^ 2 / ν by positivity)
      rw [Real.log_div (by positivity) hν.ne', Real.log_mul ha'.ne' (by positivity), Real.log_pow] at hy
      have h2 : ν * (a * s ^ 2 / ν - 1) = a * s ^ 2 - ν := by field_simp
      have h3 := mul_le_mul_of_nonneg_left hy hν.le
      rw [h2] at h3
      push_cast at h3
      unfold ph
      nlinarith
end Formalism.DimensionVariation
end

set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution (r : ℕ) (ν sv : Fin r → ℝ) (Q : ℝ) (hν : ∀ i, 0 ≤ ν i) (hs : ∀ i, 0 ≤ sv i)
    (hQ : ∑ i, sv i ^ 2 = Q) :
    (∏ i, sv i ^ ν i) * Real.exp (-Q / 2) ≤
      Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν i)) / 2) *
        Real.exp (-(1 / ((∑ i, ν i) + 1)) * Q / 2) := by
  set N := ∑ i, ν i with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => hν i
  set a : ℝ := 1 - 1 / (N + 1) with ha
  have hinv : 1 / (N + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hsplit : (∏ i, sv i ^ ν i) * Real.exp (-Q / 2) =
      (∏ i, (sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2))) * Real.exp (-(1 / (N + 1)) * Q / 2) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    have hs2 : ∑ i, -(a * sv i ^ 2) / 2 = -(a * Q) / 2 := by
      rw [← hQ, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
    rw [hs2, ha]; ring
  have hterm : ∀ i, sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2) ≤
      Real.exp (ph (ν i) / 2) * Real.exp (-(ν i * Real.log a) / 2) := by
    intro i
    refine rpow_mul_exp_neg_sq_le_exp_ph_mul_exp_log (ν i) (sv i) a (hν i) (hs i) ha0 ?_
    rcases (hν i).eq_or_lt with h | h
    · exact Or.inl h.symm
    · right
      have hNi : ν i ≤ N := Finset.single_le_sum (fun j _ => hν j) (Finset.mem_univ i)
      have hNp : 0 < N := lt_of_lt_of_le h hNi
      rw [ha]
      have : 1 / (N + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
  have hT : ∏ i, (sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2)) ≤
      Real.exp ((∑ i, ph (ν i)) / 2) * Real.exp (-(N * Real.log a) / 2) := by
    calc _ ≤ ∏ i, (Real.exp (ph (ν i) / 2) * Real.exp (-(ν i * Real.log a) / 2)) :=
          Finset.prod_le_prod (fun i _ => mul_nonneg (Real.rpow_nonneg (hs i) _) (Real.exp_pos _).le)
            (fun i _ => hterm i)
      _ = _ := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum, Finset.sum_div, hN,
            Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  have hlog : -(N * Real.log a) ≤ 1 := by
    rcases hN0.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hN1 : N + 1 ≠ 0 := (by linarith : (0:ℝ) < N + 1).ne'
      have hNne : N ≠ 0 := h0.ne'
      have haeq : a = N / (N + 1) := by
        rw [ha, eq_div_iff hN1, sub_mul, one_div, inv_mul_cancel₀ hN1]; ring
      have hapos : 0 < a := by rw [haeq]; positivity
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hapos)
      rw [Real.log_inv] at h1
      have h2 : a⁻¹ - 1 = 1 / N := by rw [haeq, inv_div]; field_simp; ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 h0.le
      rw [mul_one_div_cancel h0.ne'] at h3
      linarith
  rw [hsplit]
  calc (∏ i, (sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2))) * Real.exp (-(1 / (N + 1)) * Q / 2)
      ≤ (Real.exp ((∑ i, ph (ν i)) / 2) * Real.exp (-(N * Real.log a) / 2)) *
          Real.exp (-(1 / (N + 1)) * Q / 2) := mul_le_mul_of_nonneg_right hT (Real.exp_pos _).le
    _ ≤ Real.exp ((∑ i, ph (ν i)) / 2) * Real.exp (1 / 2) * Real.exp (-(1 / (N + 1)) * Q / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
          (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by ring
end Formalism.DimensionVariation
