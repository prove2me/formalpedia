-- Prove2me | solution 1 for Formalism.DimensionVariation.fjW_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:01.381806+00:00
-- url     : https://prove2.me/submissions/b3121220-0cef-4393-b630-f450420f1fa2

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet

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
theorem _root_.solution (a b : ℕ) (z : ℂ) : ‖fjW a b z‖ = ‖z‖ ^ (a + b) * Real.exp (-1 * ‖z‖ ^ 2) := by
  rw [fjW, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_add, neg_one_mul]
end Formalism.DimensionVariation
