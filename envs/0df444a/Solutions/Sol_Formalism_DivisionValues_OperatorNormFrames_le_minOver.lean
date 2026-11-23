-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.le_minOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:17.689052+00:00
-- url     : https://prove2.me/submissions/db5db96c-90f9-44d7-904a-3219a6cc16bb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_exists_minOver

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
theorem _root_.solution {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (a : ℝ) (h : ∀ p, a ≤ f p) :
    a ≤ minOver f := by
  obtain ⟨q, hq⟩ := exists_minOver f
  rw [hq]
  exact h q
end Formalism.DivisionValues.OperatorNormFrames
