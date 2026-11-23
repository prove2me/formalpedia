-- Prove2me | solution 1 for Formalism.DimensionVariation.fjW_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:01.032157+00:00
-- url     : https://prove2.me/submissions/7313bdce-3021-4cf8-9518-df4830abcfd9

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (n : ℕ) : ∫ z : ℂ, fjW n n z = (π : ℂ) * (n ! : ℂ) := by
  have h : ∀ z : ℂ, fjW n n z =
      ((‖z‖ ^ (2 * n) * Real.exp (-1 * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    intro z
    rw [neg_one_mul, Complex.ofReal_mul, Complex.ofReal_pow, pow_mul, fjW, ← mul_pow,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  rw [integral_complex_ofReal, (fjMoment 1 one_pos (2 * n)).2]
  have hG : ((((2 * n : ℕ) : ℝ) + 2) / 2) = (n : ℝ) + 1 := by push_cast; ring
  rw [hG, Real.one_rpow, mul_one, Real.Gamma_nat_eq_factorial, Complex.ofReal_mul,
    Complex.ofReal_natCast]
end Formalism.DimensionVariation
