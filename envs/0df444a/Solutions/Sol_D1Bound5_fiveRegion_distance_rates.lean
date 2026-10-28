-- Prove2me | solution 1 for D1Bound5.fiveRegion_distance_rates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:55:39.130652+00:00
-- url     : https://prove2.me/submissions/6c34ce52-90f7-4976-a559-1d8b0e5bae0b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Theorems.Thm_D1Bound5_finite_distance_max_norm_le_ratio
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg

section
namespace D1Bound5



/-- All five finite residual rates are derived from actual anchor
moduli, with no lower bound on their separation. -/
theorem _root_.solution (region : Fin 5) (x y : ℂ)
    (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖) :
    (101/2560 : ℝ)*max (‖x-y‖^4) (‖x‖*‖x-y‖^3) ≤ fiveRegionN2Residual region*‖y‖^4 ∧
    (3535/409600 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5) ≤ fiveRegionN3Residual region*‖y‖^6 ∧
    (707/40960 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5) ≤ fiveRegionA3Residual region*‖y‖^6 ∧
    (6363/409600 : ℝ)*max (‖x-y‖^8) (‖x‖*‖x-y‖^7) ≤ fiveRegionA4Residual region*‖y‖^8 ∧
    (9999/2621440 : ℝ)*max (‖x-y‖^10) (‖x‖*‖x-y‖^9) ≤ fiveRegionA5Residual region*‖y‖^10 := by
  have hh (n : ℕ) (hn : 1 ≤ n) := finite_distance_max_norm_le_ratio x y
    (fiveRegionAnchorRatio region) n (fiveRegionAnchorRatio_nonneg region) hn hxy
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [fiveRegionN2Residual,mul_assoc] using
      mul_le_mul_of_nonneg_left (hh 4 (by decide)) (by norm_num : (0 : ℝ) ≤ 101/2560)
  · simpa only [fiveRegionN3Residual,mul_assoc] using
      mul_le_mul_of_nonneg_left (hh 6 (by decide)) (by norm_num : (0 : ℝ) ≤ 3535/409600)
  · simpa only [fiveRegionA3Residual,mul_assoc] using
      mul_le_mul_of_nonneg_left (hh 6 (by decide)) (by norm_num : (0 : ℝ) ≤ 707/40960)
  · simpa only [fiveRegionA4Residual,mul_assoc] using
      mul_le_mul_of_nonneg_left (hh 8 (by decide)) (by norm_num : (0 : ℝ) ≤ 6363/409600)
  · simpa only [fiveRegionA5Residual,mul_assoc] using
      mul_le_mul_of_nonneg_left (hh 10 (by decide)) (by norm_num : (0 : ℝ) ≤ 9999/2621440)

end D1Bound5
end
