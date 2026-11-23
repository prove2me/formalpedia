-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.minOver_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:59.228813+00:00
-- url     : https://prove2.me/submissions/82edeeac-19e8-4cf9-b01e-5fb42b643226

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
theorem _root_.solution {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (p : Ix) : minOver f ≤ f p := by
  unfold minOver
  apply Finset.inf'_le
  exact Finset.mem_univ p
end Formalism.DivisionValues.OperatorNormFrames
