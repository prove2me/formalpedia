-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.embG_mul_mMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:33:01.227443+00:00
-- url     : https://prove2.me/submissions/403a934c-73b8-41e6-b279-dd536fc883d6

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
    embG k j ρ y * mMap k j ρ Z γ = mMap k j ρ Z (y * γ) := by
  unfold mMap embG
  rw [block3_mul]
  congr 1 <;> simp
end Formalism.FourierDecayAlt.P.Ux4
