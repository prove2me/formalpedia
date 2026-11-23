-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.cnt_msk_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:36.855531+00:00
-- url     : https://prove2.me/submissions/995553b6-a6ac-4f22-b076-6d806dedfb66

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_msk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_msk_msk

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
theorem _root_.solution {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (Z : Matrix (Fin n) (Fin n) K)
    (x : Fin n → R) : msk k (D *ᵥ abelian₂ R k Z x) = D *ᵥ abelian₂ R k Z x := by
  rw [Lam_apply, isD_mulVec_msk R k hD, msk_msk]
end Formalism.FourierDecayAlt.P.A5x9
