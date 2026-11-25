-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:24:29.583835+00:00
-- url     : https://prove2.me/submissions/d0602d9e-750a-42c8-a795-3628f7cf3f86

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
theorem _root_.solution {K : Type} [Field K] {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (hP : Function.Surjective P.mulVec) :
    ∃ ρ : (Fin D → K) →ₗ[K] (Fin n → K), ∀ y, P.mulVec (ρ y) = y := by
  obtain ⟨g, hg⟩ :=
    (Matrix.mulVecLin P).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hP)
  exact ⟨g, fun y => by simpa using LinearMap.congr_fun hg y⟩
end Formalism.DivisionValues.OperatorNormFrames
