-- Prove2me | solution 1 for Eden.totalDegree_ratePolynomial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:01.881775+00:00
-- url     : https://prove2.me/submissions/14667ed6-ba77-4ba5-b11e-303098b6cb81

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
import Theorems.Thm_Eden_totalDegree_radiusPolynomial_le

set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial
namespace Eden
theorem _root_.solution (i j : Fin 5) :
    (ratePolynomial i j).totalDegree ≤ 4 := by
  have h₁ := (totalDegree_sub_C_le (radiusPolynomial i j) (1 : ℝ)).trans
    (totalDegree_radiusPolynomial_le i j)
  have h₂ := (totalDegree_sub_C_le (radiusPolynomial i j) (2 : ℝ)).trans
    (totalDegree_radiusPolynomial_le i j)
  have h := totalDegree_mul (-(radiusPolynomial i j - C (1 : ℝ)))
    (radiusPolynomial i j - C (2 : ℝ))
  rw [totalDegree_neg] at h
  exact h.trans (by omega)
end Eden
