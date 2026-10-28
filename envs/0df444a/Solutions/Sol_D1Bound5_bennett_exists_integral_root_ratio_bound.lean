-- Prove2me | solution 1 for D1Bound5.bennett_exists_integral_root_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:24.271632+00:00
-- url     : https://prove2.me/submissions/27dfc204-44c1-4f70-9268-53f2111ad021

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
import Theorems.Thm_D1Bound5_bennett_two_root_branch_norm_lt
import Theorems.Thm_D1Bound5_bennett_two_root_branch_sq_ne_zero

section
namespace D1Bound5







/-- A uniform root-transfer estimate with the same final constant3 as the
manuscript. The stronger entry bounds permit the simple factor3/2 here,
avoiding a monotonicity argument for the auxiliary function e(X). -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a c d z r v : R)
    (ha : f a ≠ 0) (hc : f c ≠ 0) (hz : f z ≠ 0)
    (hr : r ^ 2 = a * c + 1) (hv : v ^ 2 = a * d + 1)
    (hzsq : z ^ 2 = c * d + 1)
    (hAC : 1000 ≤ ‖f a‖ * ‖f c‖) (hC : 4 * ‖f a‖ ≤ ‖f c‖) :
    ∃ s : R, (s = r * v ∨ s = -(r * v)) ∧
      ‖(1 + 1 / (f a * f c)) ^ (1 / 2 : ℂ) - f s / (f a * f z)‖ <
        (3 / 2 : ℝ) * ‖f c‖ / (‖f a‖ * ‖f z‖ ^ 2) := by
  let θ : ℂ := (1 + 1 / (f a * f c)) ^ (1 / 2 : ℂ)
  obtain ⟨hθsq, hθ0⟩ := bennett_two_root_branch_sq_ne_zero (f a) (f c) (by linarith)
  obtain ⟨s, hs, _, herr⟩ := bennett_exists_integral_root_ratio f a c d z r v θ
    ha hc hz hθ0 hr hv hzsq hθsq
  have hθnorm : ‖θ‖ < 6 / 5 := bennett_two_root_branch_norm_lt (f a) (f c) hAC
  have hdiff : ‖f c - f a‖ ≤ (5 / 4 : ℝ) * ‖f c‖ := by
    have ht := norm_sub_le (f c) (f a)
    linarith
  have hnum : ‖θ‖ * ‖f c - f a‖ < (3 / 2 : ℝ) * ‖f c‖ := by
    calc
      _ ≤ ‖θ‖ * ((5 / 4 : ℝ) * ‖f c‖) :=
        mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
      _ < (6 / 5 : ℝ) * ((5 / 4) * ‖f c‖) :=
        mul_lt_mul_of_pos_right hθnorm
          (mul_pos (by norm_num) (norm_pos_iff.mpr hc))
      _ = _ := by ring
  refine ⟨s, hs, herr.trans_lt ?_⟩
  exact div_lt_div_of_pos_right hnum
    (mul_pos (norm_pos_iff.mpr ha) (sq_pos_of_pos (norm_pos_iff.mpr hz)))



end D1Bound5
end
