-- Prove2me | solution 1 for FourierJacobi.Algebra.one_sub_mul_ne_zero_of_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:35.29593+00:00
-- url     : https://prove2.me/submissions/743f1ded-ff92-4736-9939-6466b85ec1f0

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {z x : ℂ}
    (hz : ‖z‖ = 1) (hx : ‖x‖ < 1) : 1 - z * x ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one, norm_mul, hz, one_mul] at hh
  linarith
end FourierJacobi.Algebra
