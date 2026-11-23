-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.compA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:40.316668+00:00
-- url     : https://prove2.me/submissions/2800865b-f7d1-45b2-a675-139604d5e4f2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absNb

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
theorem _root_.solution (hLN : LevNab) (hLF : LevFns) (P : Par) (u v : ℂ) :
    (ggA P * xA P u * l0A P u) * (ggA P * xA P v * l0A P v) =
      (ggA P * xA P v * l0A P v) * (ggA P * xA P u * l0A P u) := by
  obtain ⟨_, _, hNzb, _, hNG, hNGi, _⟩ := hLN P
  obtain ⟨hcomm, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  have mzb : zbA P ∈ fnsA P := by unfold fnsA; simp
  have mG : ggA P ∈ fnsA P := by unfold fnsA; simp
  have mGi : ggiA P ∈ fnsA P := by unfold fnsA; simp
  have hGb : ggA P * (zbA P * ggiA P) = zbA P := by
    rw [← mul_assoc, hcomm _ mG _ mzb, mul_assoc, hGGi, mul_one]
  have hbG : (zbA P * ggiA P) * ggA P = ggA P * (zbA P * ggiA P) := by
    rw [hGb, mul_assoc, hGiG, mul_one]
  have hNb : nabA P * (zbA P * ggiA P) = (zbA P * ggiA P) * nabA P - (zbA P * ggiA P) * (zbA P * ggiA P) :=
    absNb _ _ _ hNzb hNGi (hcomm _ mGi _ mzb)
  have cX : ∀ w : ℂ, Commute (xA P w) (ggA P) ∧ Commute (xA P w) (zbA P * ggiA P) ∧ Commute (xA P w) (nabA P) ∧
      Commute (xA P w) (zbA P) := fun w =>
    ⟨kap_comm_sc P _ _, (kap_comm_sc P _ _).mul_right (kap_comm_sc P _ _), kap_comm_nab P _, kap_comm_sc P _ _⟩
  have hXX : xA P u * xA P v = xA P v * xA P u := (kap_comm_kap P _ _).eq
  rw [lowering_constant_eq_shift, lowering_constant_eq_shift,
    absA _ _ _ _ _ _ hNG hbG (cX v).1 (cX v).2.1 (cX v).2.2.1 (cX v).2.2.2,
    absA _ _ _ _ _ _ hNG hbG (cX u).1 (cX u).2.1 (cX u).2.2.1 (cX u).2.2.2,
    absW _ _ _ _ hGb hNb, absW _ _ _ _ hGb hNb, hXX,
    add_comm (u + 1 / 2) (v + 1 / 2), mul_comm (u + 1 / 2) (v + 1 / 2)]
end Formalism.FourierDecayAlt.P.Mx7
