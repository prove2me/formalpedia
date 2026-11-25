-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.wSer_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:38.205178+00:00
-- url     : https://prove2.me/submissions/e899d22d-fa8c-4694-ac41-1326092b653e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_psi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_weq_phi
import Theorems.Thm_Formalism_L2_Th1_A_ISer_eq_wSer_subst
import Theorems.Thm_Formalism_L2_Th1_A_wSerSpec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution : (wSer (C • W)).subst (phi W C) = psi W C :=
  (ISer.eq_wSer_subst wSerSpec (C • W) _ _ (phi_cc W C) (psi_cc W C) (weq_phi W C)).symm
end Formalism.L2.KerInert.VC
