-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.Lam_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:09.218353+00:00
-- url     : https://prove2.me/submissions/5b3b8bc9-3a86-4f39-9680-93ea7e96a615

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_msk_mulVec

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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R) :
    abelian₂ R k (Z₀ * p) x = b22 k p⁻¹ *ᵥ abelian₂ R k Z₀ x := by
  rw [Lam_apply, Lam_apply, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, msk_mulVec k hp.2.1]
end Formalism.FourierDecayAlt.P.A5x9
