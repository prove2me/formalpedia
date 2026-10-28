-- Prove2me | solution 1 for D1Bound5.bennett_exists_integral_root_ratio_bound_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:23:05.380217+00:00
-- url     : https://prove2.me/submissions/c3f54d7e-8840-452d-8a0d-ace83fa2f267

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio
import Theorems.Thm_D1Bound5_bennett_two_root_branch_sq_ne_zero

section
namespace D1Bound5

/-- The finite-family root comparison retains one sign of the original
integral product. The larger anchor separation improves the factor from
3/2 to the manuscript's101/100. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a c d z r v : R)
    (ha : f a ≠ 0) (hc : f c ≠ 0) (hz : f z ≠ 0)
    (hr : r^2 = a*c+1) (hv : v^2 = a*d+1) (hzsq : z^2 = c*d+1)
    (hAC : 1000 ≤ ‖f a‖*‖f c‖) (hC : 200*‖f a‖ ≤ ‖f c‖) :
    ∃ s : R, (s = r*v ∨ s = -(r*v)) ∧
      ‖(1+1/(f a*f c))^(1/2 : ℂ)-f s/(f a*f z)‖ <
        (101/100 : ℝ)*‖f c‖/(‖f a‖*‖f z‖^2) := by
  let θ : ℂ := (1+1/(f a*f c))^(1/2 : ℂ)
  obtain ⟨hθsq,hθ0⟩ := bennett_two_root_branch_sq_ne_zero
    (f a) (f c) (by linarith)
  obtain ⟨s,hs,_,herr⟩ := bennett_exists_integral_root_ratio f a c d z r v θ
    ha hc hz hθ0 hr hv hzsq hθsq
  have hthetaSq : ‖θ‖^2 ≤ (1001/1000 : ℝ) := by
    have hn : ‖θ‖^2 = ‖1+1/(f a*f c)‖ := by
      rw [← norm_pow]
      exact congrArg norm hθsq
    rw [hn]
    calc
      _ ≤ ‖(1 : ℂ)‖+‖1/(f a*f c)‖ := norm_add_le _ _
      _ = 1+1/(‖f a‖*‖f c‖) := by simp only [norm_one,norm_div,norm_mul]
      _ ≤ 1+1/(1000 : ℝ) := by
        gcongr
      _ = _ := by norm_num
  have htheta : ‖θ‖ < (1001/1000 : ℝ) := by nlinarith [norm_nonneg θ]
  have hdiff : ‖f c-f a‖ ≤ (201/200 : ℝ)*‖f c‖ := by
    have ht := norm_sub_le (f c) (f a)
    linarith
  have hCpos : 0 < ‖f c‖ := norm_pos_iff.mpr hc
  have hnum : ‖θ‖*‖f c-f a‖ < (101/100 : ℝ)*‖f c‖ := by
    calc
      _ ≤ ‖θ‖*((201/200 : ℝ)*‖f c‖) :=
        mul_le_mul_of_nonneg_left hdiff (norm_nonneg θ)
      _ < (1001/1000 : ℝ)*((201/200 : ℝ)*‖f c‖) :=
        mul_lt_mul_of_pos_right htheta (by positivity)
      _ < _ := by nlinarith only [hCpos]
  refine ⟨s,hs,herr.trans_lt ?_⟩
  exact div_lt_div_of_pos_right hnum
    (mul_pos (norm_pos_iff.mpr ha) (sq_pos_of_pos (norm_pos_iff.mpr hz)))

end D1Bound5
end
