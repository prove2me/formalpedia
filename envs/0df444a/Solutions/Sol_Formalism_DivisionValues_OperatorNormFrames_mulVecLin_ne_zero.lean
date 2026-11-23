-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.mulVecLin_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:57.430612+00:00
-- url     : https://prove2.me/submissions/208a1604-9738-41d2-b5c5-75d8d63fc89d

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
theorem _root_.solution {K : Type} [Field K] {a b : ℕ} (N : Matrix (Fin b) (Fin a) K) (h : N ≠ 0) :
    Matrix.mulVecLin N ≠ 0 := by
  intro h0
  apply h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h0
  simpa using this
end Formalism.DivisionValues.OperatorNormFrames
