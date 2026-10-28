-- Prove2me | solution 1 for D1Bound5.coherent_cpow_half_near_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:46:14.200991+00:00
-- url     : https://prove2.me/submissions/670b1fb6-1277-448e-9df9-d86b66f75fe1

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_coherent_cpow_half_sub_one_norm_le

section
open Finset

namespace D1Bound5



/-- The four near-one estimates in the manuscript, for the actual
analytic branch.  Rationalization uses its exact square and the small
binomial remainder, rather than any assumed sign of a square root. -/
theorem _root_.solution
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ < (1 / 10000 : ℝ)) :
    (99 / 100 : ℝ) < ‖(1 + w) ^ (1 / 2 : ℂ)‖ ∧
    ‖(1 + w) ^ (1 / 2 : ℂ)‖ < (101 / 100 : ℝ) ∧
    (100 / 201 : ℝ) * ‖w‖ < ‖1 - (1 + w) ^ (1 / 2 : ℂ)‖ ∧
    ‖1 - (1 + w) ^ (1 / 2 : ℂ)‖ < (100 / 199 : ℝ) * ‖w‖ := by
  let u : ℂ := (1 + w) ^ (1 / 2 : ℂ)
  let d : ℝ := ‖u - 1‖
  have hw1 : ‖w‖ < 1 := by linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd : d < (1 / 100 : ℝ) := by
    have hb := coherent_cpow_half_sub_one_norm_le w hw1
    have hrat : (1 / 2 : ℝ) * ‖w‖ / (1 - ‖w‖) < (1 / 100 : ℝ) := by
      apply (div_lt_iff₀ (by linarith : 0 < 1 - ‖w‖)).2
      nlinarith only [hw]
    exact hb.trans_lt hrat
  have hdrev : ‖(1 : ℂ) - u‖ = d := norm_sub_rev _ _
  have huupper : ‖u‖ ≤ 1 + d := by
    have h := norm_add_le (1 : ℂ) (u - 1)
    have heq : (1 : ℂ) + (u - 1) = u := by ring
    rw [heq, norm_one] at h
    exact h
  have hulower : 1 ≤ ‖u‖ + d := by
    have h := norm_sub_le u (u - 1)
    have heq : u - (u - 1) = (1 : ℂ) := by ring
    rw [heq, norm_one] at h
    exact h
  have hBupper : ‖(1 : ℂ) + u‖ < (201 / 100 : ℝ) := by
    have h := norm_add_le (2 : ℂ) (u - 1)
    have heq : (2 : ℂ) + (u - 1) = 1 + u := by ring
    rw [heq, Complex.norm_two] at h
    change ‖(1 : ℂ) + u‖ ≤ 2 + d at h
    linarith
  have hBlower : (199 / 100 : ℝ) < ‖(1 : ℂ) + u‖ := by
    have h := norm_sub_le ((1 : ℂ) + u) (u - 1)
    have heq : (1 : ℂ) + u - (u - 1) = 2 := by ring
    rw [heq, Complex.norm_two] at h
    change 2 ≤ ‖(1 : ℂ) + u‖ + d at h
    linarith
  have hsq : u ^ 2 = 1 + w := coherent_cpow_half_sq (1 + w)
  have hprod : ((1 : ℂ) - u) * (1 + u) = -w := by
    linear_combination -hsq
  have hnorm : d * ‖(1 : ℂ) + u‖ = ‖w‖ := by
    have h := congrArg norm hprod
    simpa only [norm_mul, norm_neg, hdrev] using h
  have hdpos : 0 < d := by
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    by_contra h
    have hz : d = 0 := by linarith
    rw [hz, zero_mul] at hnorm
    linarith
  have hdistlower : (100 / 201 : ℝ) * ‖w‖ < d := by
    have h := mul_lt_mul_of_pos_left hBupper hdpos
    rw [hnorm] at h
    linarith
  have hdistupper : d < (100 / 199 : ℝ) * ‖w‖ := by
    have h := mul_lt_mul_of_pos_left hBlower hdpos
    rw [hnorm] at h
    linarith
  change (99 / 100 : ℝ) < ‖u‖ ∧ ‖u‖ < (101 / 100 : ℝ) ∧
    (100 / 201 : ℝ) * ‖w‖ < ‖1 - u‖ ∧
    ‖1 - u‖ < (100 / 199 : ℝ) * ‖w‖
  rw [hdrev]
  exact ⟨by linarith, by linarith, hdistlower, hdistupper⟩

end D1Bound5
end
