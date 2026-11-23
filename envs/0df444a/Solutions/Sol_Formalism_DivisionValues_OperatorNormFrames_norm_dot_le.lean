-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.norm_dot_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:19.56387+00:00
-- url     : https://prove2.me/submissions/8d072d0b-6674-4d2b-ac57-7d913aa3a146

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
theorem _root_.solution {n : ℕ} (y w : Fin n → ℂ) :
    ‖y ⬝ᵥ w‖ ≤ Formalism.HermitianLatticesTheory.cnorm y * Formalism.HermitianLatticesTheory.cnorm w := by
  have h1 : ‖y ⬝ᵥ w‖ ≤ ∑ i, ‖y i‖ * ‖w i‖ := by
    first
      | simpa [dotProduct, norm_mul] using norm_sum_le Finset.univ fun i => y i * w i
      | simpa [Matrix.dotProduct, norm_mul] using norm_sum_le Finset.univ fun i => y i * w i
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
end Formalism.DivisionValues.OperatorNormFrames
