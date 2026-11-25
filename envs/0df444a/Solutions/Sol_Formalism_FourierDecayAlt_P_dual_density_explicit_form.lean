-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_density_explicit_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:29.237086+00:00
-- url     : https://prove2.me/submissions/e47cf043-d2b5-4afc-aad6-571bb1788d50

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos_idx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
open LocalVolumePositivity
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : DstarProductFormula := by
  intro P _ B hP hI
  have hKpp := pos_μKpp hP
  have hidx := pos_idx hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hK : B.μK = (∏ p, B.gg p / (B.nn p * B.uk p)) * B.μKpp := by
    unfold MassData.μK MassData.μKpp
    have : ∏ p, B.μKp p = ∏ p, (B.gg p / (B.nn p * B.uk p) * B.μKppp p) :=
      prod_congr rfl fun p _ => (hI p).1
    rw [this, prod_mul_distrib]; ring
  unfold MassData.Dstar MassData.V0
  rw [hK]
  field_simp
end Formalism.FourierDecayAlt.P
