-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_principal_inverseSqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:58.102797+00:00
-- url     : https://prove2.me/submissions/8ad591c8-28a3-47f1-90f1-b555578a0ca3

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_finite_principal_unitary
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b d) *
      principalNormalizer (inverseSqrt q : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * (inverseSqrt q : ℂ)) * (1 + (inverseSqrt q : ℂ) / d)) :=
  finite_principal_unitary q (inverseSqrt q) a b d
    (le_of_lt (inverseSqrt_pos hq)) (inverseSqrt_lt_one hq) ha hb hd ha₁ hb₁ hab hab₁
end FourierJacobi.Algebra
