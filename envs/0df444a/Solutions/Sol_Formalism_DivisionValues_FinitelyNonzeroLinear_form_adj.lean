-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.form_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:52.260944+00:00
-- url     : https://prove2.me/submissions/a8384c58-084e-4c64-8418-2b41f1bdbaf0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {A A' : Matrix (Fin n) (Fin n) ℂ} (h : Aᴴ * Hc = Hc * A') (u v : Fin n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ Hc *ᵥ v = star u ⬝ᵥ Hc *ᵥ (A' *ᵥ v) := by
  simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h]
end Formalism.DivisionValues.FinitelyNonzeroLinear
