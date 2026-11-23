-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.pairC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:11.817793+00:00
-- url     : https://prove2.me/submissions/40348233-543f-48ac-a47d-76b815ebd581

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    pairC v B x y = y ⬝ᵥ (pmat v B).mulVec x := by
  first
    | simp only [pairC, pmat, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    | simp only [pairC, pmat, Matrix.dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.DivisionValues.OperatorNormFrames
