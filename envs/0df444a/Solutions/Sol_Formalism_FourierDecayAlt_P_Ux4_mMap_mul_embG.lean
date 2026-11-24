-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:31.529043+00:00
-- url     : https://prove2.me/submissions/539d41a2-b5db-4d5d-8afe-0a6467780979

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    mMap k j ρ Z γ * embG k j ρ y = mMap k j ρ Z (γ * y) := by
  unfold mMap embG
  rw [block3_mul]
  congr 1 <;> simp
end Formalism.FourierDecayAlt.P.Ux4
