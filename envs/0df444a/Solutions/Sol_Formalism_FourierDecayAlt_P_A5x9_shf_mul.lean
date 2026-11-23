-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:31.424464+00:00
-- url     : https://prove2.me/submissions/044c8eae-1c00-4c56-8f87-c08163354e41

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
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (m : Fin n → R)
    (β : Fin n → K) :
    Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p) =
      Z₀ * p + vecMulVec (coeLin R m) (β ᵥ* p) := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.A5x9
