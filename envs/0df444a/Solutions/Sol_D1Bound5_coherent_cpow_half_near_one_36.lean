-- Prove2me | solution 1 for D1Bound5.coherent_cpow_half_near_one_36
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:49.322618+00:00
-- url     : https://prove2.me/submissions/59cb3637-9a91-4f82-b2cc-1e85ffc5e4dd

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_coherent_cpow_half_sub_one_norm_le

section
open Finset

namespace D1Bound5

/-- The broader near-one estimates needed by the general three-anchor
lemma.  The analytic branch is fixed by the convergent binomial series. -/
theorem _root_.solution
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ ≤ (1 / 36 : ℝ)) :
    (35 / 36 : ℝ) < ‖(1 + w) ^ (1 / 2 : ℂ)‖ ∧
    ‖(1 + w) ^ (1 / 2 : ℂ)‖ < (37 / 36 : ℝ) ∧
    ‖1 - (1 + w) ^ (1 / 2 : ℂ)‖ < (36 / 71 : ℝ) * ‖w‖ := by
  let u : ℂ := (1 + w) ^ (1 / 2 : ℂ)
  let d : ℝ := ‖u - 1‖
  have hw1 : ‖w‖ < 1 := by linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd : d < (1 / 36 : ℝ) := by
    have hb := coherent_cpow_half_sub_one_norm_le w hw1
    have hrat : (1 / 2 : ℝ) * ‖w‖ / (1 - ‖w‖) < (1 / 36 : ℝ) := by
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
  have hBlower : (71 / 36 : ℝ) < ‖(1 : ℂ) + u‖ := by
    have h := norm_sub_le ((1 : ℂ) + u) (u - 1)
    have heq : (1 : ℂ) + u - (u - 1) = 2 := by ring
    rw [heq, Complex.norm_two] at h
    change 2 ≤ ‖(1 : ℂ) + u‖ + d at h
    linarith
  have hsq : u ^ 2 = 1 + w := coherent_cpow_half_sq (1 + w)
  have hprod : ((1 : ℂ) - u) * (1 + u) = -w := by linear_combination -hsq
  have hnorm : d * ‖(1 : ℂ) + u‖ = ‖w‖ := by
    simpa only [norm_mul, norm_neg, hdrev] using congrArg norm hprod
  have hdpos : 0 < d := by
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    by_contra h
    have hz : d = 0 := by linarith
    rw [hz, zero_mul] at hnorm
    linarith
  have hdist : d < (36 / 71 : ℝ) * ‖w‖ := by
    have h := mul_lt_mul_of_pos_left hBlower hdpos
    rw [hnorm] at h
    linarith
  change (35 / 36 : ℝ) < ‖u‖ ∧ ‖u‖ < (37 / 36 : ℝ) ∧
    ‖1-u‖ < (36 / 71 : ℝ) * ‖w‖
  rw [hdrev]
  exact ⟨by linarith, by linarith, hdist⟩









end D1Bound5
end
