-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:17.45908+00:00
-- url     : https://prove2.me/submissions/1cd4b0b9-00dc-4c21-9b3a-2279d0d0d922

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsUpUni p) (β v : Fin n → K) :
    (β ᵥ* p) ⬝ᵥ ((Z₀ * p)⁻¹ *ᵥ v) = β ⬝ᵥ (Z₀⁻¹ *ᵥ v) := by
  have hdp : IsUnit p.det := by rw [isUpUni_det K hp]; exact isUnit_one
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdp, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.A5x9
