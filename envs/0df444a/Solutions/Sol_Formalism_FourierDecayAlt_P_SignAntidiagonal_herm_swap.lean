-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:43.336515+00:00
-- url     : https://prove2.me/submissions/9f11cf65-42b2-4aa1-a74c-66b48b6cb56f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext p q
    rw [conjTranspose_apply, hpk_star]
  rw [star_dotProduct v (Hpk k r *ᵥ w), star_star, star_mulVec, hH, dotProduct_mulVec]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
