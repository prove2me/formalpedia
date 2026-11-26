-- Prove2me | solution 1 for FourierJacobi.Algebra.coe_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:35.750684+00:00
-- url     : https://prove2.me/submissions/343a5bb0-0f94-4953-aaa1-105aa892f4c3

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
theorem _root_.solution {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ‖(t : ℂ)‖ < 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀] using ht₁
end FourierJacobi.Algebra
