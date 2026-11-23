-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.l_mul_t22_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:49.49298+00:00
-- url     : https://prove2.me/submissions/132824c0-3b94-453a-a488-a69eccfc37eb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_intertwine_gamma
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absLG2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_Ul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lower_shift_commute_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kappa_commute_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kappa_commute_l0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (P : Par) (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    lA P Y * t22 P (Y + 1) = t22 P (Y + 1) * lA P (Y + 1) := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  obtain ⟨_, _, _, _, nG, _, _⟩ := hLN P
  have cGzb : Commute (ggA P) (zbA P) := fn_comm P _ _ _ _
  have cGGi : Commute (ggA P) (ggiA P) := fn_comm P _ _ _ _
  have hGb : ggA P * (zbA P * ggiA P) = zbA P := by rw [← mul_assoc, cGzb.eq, mul_assoc, hGGi, mul_one]
  have hbG : (zbA P * ggiA P) * ggA P = ggA P * (zbA P * ggiA P) := (cGzb.mul_right cGGi).eq.symm
  have hLG : l0A P Y * ggA P = ggA P * l0A P (Y + 1) := by
    rw [lowering_constant_eq_shift, lowering_constant_eq_shift]
    exact absLG2 _ _ _ _ nG hbG hGb _ _ (by ring)
  rw [lA_eq, lA_eq, t22]
  exact lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_l0 P _ _) (lower_shift_commute_coordinate hSh hR P Y h0 h1) (sc_Ul hSc P _ _)
    (kap_comm_sc P _ _).symm cGGi
end Formalism.FourierDecayAlt.P.Mx7
