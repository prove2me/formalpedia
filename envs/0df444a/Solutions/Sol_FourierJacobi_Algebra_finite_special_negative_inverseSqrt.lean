-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_special_negative_inverseSqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:56.852466+00:00
-- url     : https://prove2.me/submissions/483a97cf-095c-44fc-8c91-b609bc0ef47d

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_finite_special_negative_unitary
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b (-(inverseSqrt q : ℂ))) *
      specialNormalizer (inverseSqrt q : ℂ) a b (-1) = 2 / ((q : ℂ) + 1) :=
  finite_special_negative_unitary q (inverseSqrt q) a b
    (inverseSqrt_pos hq) (inverseSqrt_lt_one hq) ha hb ha₁ hb₁ hab hab₁ hA hB
end FourierJacobi.Algebra
