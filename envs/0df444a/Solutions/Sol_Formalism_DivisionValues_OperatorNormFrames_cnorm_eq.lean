-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.cnorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:59.4074+00:00
-- url     : https://prove2.me/submissions/ad018a83-45b6-4a88-a8f6-c44b3ec73e2e

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
theorem _root_.solution {n : ℕ} (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.cnorm]
end Formalism.DivisionValues.OperatorNormFrames
