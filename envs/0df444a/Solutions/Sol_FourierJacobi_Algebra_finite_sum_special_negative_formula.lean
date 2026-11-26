-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_sum_special_negative_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:23.744259+00:00
-- url     : https://prove2.me/submissions/a22090ef-60b2-4fb9-bf7a-78ed73bba582

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Theorems.Thm_FourierJacobi_Algebra_finiteCore_eq_closedCore
import Theorems.Thm_FourierJacobi_Algebra_normalized_closedCore_special_negative


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (q t a b : K)
    (h : FiniteRegular t a b (-t))
    (ht₀ : t ≠ 0) (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    (2 / (q + 1) * finiteCore t a b (-t)) * specialNormalizer t a b (-1) =
      2 / (q + 1) := by
  rw [finiteCore_eq_closedCore t a b (-t) h, mul_assoc,
    normalized_closedCore_special_negative t a b ht₀ h.a_ne_zero h.b_ne_zero
      hc hp hn₁ hn₂ hf ht ht₄, mul_one]
end FourierJacobi.Algebra
