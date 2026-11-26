-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_principal_square_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:19.106634+00:00
-- url     : https://prove2.me/submissions/828c3fe7-3c0d-450d-ba6d-a5e711add7d3

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_square_root_satake
import Theorems.Thm_FourierJacobi_Algebra_finite_principal_inverseSqrt
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b d A B : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hA : A ^ 2 = a) (hB : B ^ 2 = b)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b d) *
      principalNormalizer (inverseSqrt q : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (A⁻¹ + A) ^ 2 * (B⁻¹ + B) ^ 2 /
        ((1 + d * (inverseSqrt q : ℂ)) * (1 + (inverseSqrt q : ℂ) / d)) := by
  rw [square_root_satake a A (unit_ne_zero ha) hA,
    square_root_satake b B (unit_ne_zero hb) hB]
  exact finite_principal_inverseSqrt q hq a b d ha hb hd ha₁ hb₁ hab hab₁
end FourierJacobi.Algebra
