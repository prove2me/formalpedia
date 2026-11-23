-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.cnorm_sq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:33.698334+00:00
-- url     : https://prove2.me/submissions/5f3d6501-997b-45da-b55d-d24a6ffef81b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_star_dot_self

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
theorem _root_.solution {n d : ℕ} (Z : Matrix (Fin d) (Fin n) ℂ) (y : Fin n → ℂ) :
    ((Formalism.HermitianLatticesTheory.cnorm (Z.mulVec y) ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ (Zᴴ * Z).mulVec y := by
  rw [← star_dot_self, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
end Formalism.DivisionValues.OperatorNormFrames
