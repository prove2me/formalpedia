-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_sum_principal_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:22.849337+00:00
-- url     : https://prove2.me/submissions/f0455a0c-1369-4a11-9307-23e8430ab4af

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Theorems.Thm_FourierJacobi_Algebra_finiteCore_eq_closedCore
import Theorems.Thm_FourierJacobi_Algebra_normalized_closedCore_principal
import Theorems.Thm_FourierJacobi_Algebra_satakeNumerator_eq


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (q t a b d : K)
    (h : FiniteRegular t a b d)
    (hc : poincare t ≠ 0) (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hd₁ : d₁ t a b d ≠ 0) (hd₂ : d₂ t a b d ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    (2 / (q + 1) * finiteCore t a b d) * principalNormalizer t a b d =
      2 / (q + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * t) * (1 + t / d)) := by
  rw [finiteCore_eq_closedCore t a b d h, mul_assoc,
    normalized_closedCore_principal t a b d hc hn₁ hn₂ hd₁ hd₂ ht hm hp him hip,
    satakeNumerator_eq a b h.a_ne_zero h.b_ne_zero]
  ring
end FourierJacobi.Algebra
