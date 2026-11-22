-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.star_dot_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:34.961877+00:00
-- url     : https://prove2.me/submissions/dcfeb395-1d85-4005-b5b9-f188ddf61d6a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {n : ℕ} (w : Fin n → ℂ) :
    star w ⬝ᵥ w = ((Formalism.HermitianLatticesTheory.cnorm w ^ 2 : ℝ) : ℂ) := by
  have h : Formalism.HermitianLatticesTheory.cnorm w ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  rw [h]
  push_cast
  first
    | simp only [dotProduct, Pi.star_apply]
    | simp only [Matrix.dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact Complex.conj_mul' (w i)
    | exact_mod_cast Complex.conj_mul' (w i)
    | exact RCLike.conj_mul (w i)
end Formalism.DivisionValues.OperatorNormFrames
