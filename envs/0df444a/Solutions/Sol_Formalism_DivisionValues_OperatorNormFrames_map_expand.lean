-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.map_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:57.521743+00:00
-- url     : https://prove2.me/submissions/93578447-ffd4-4753-9028-9b19597b3221

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
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {K : Type} [Field K] {a D : ℕ} (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (φ : Fin a → K) (e : Fin D → K) : B φ e = ∑ i, φ i * B (Pi.single i 1) e := by
  have hφ : φ = ∑ i, φ i • Pi.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hφ]
  simp [map_sum, map_smul, LinearMap.sum_apply]
end Formalism.DivisionValues.OperatorNormFrames
