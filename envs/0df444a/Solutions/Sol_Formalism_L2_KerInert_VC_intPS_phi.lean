-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.intPS_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:26.734475+00:00
-- url     : https://prove2.me/submissions/162b26d0-4c60-4c15-b6d2-4acb0a7a059e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_den_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_den_mul_vv
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_C__71fb3c266dee
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_X__29e7674ada74
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_add__10f45f09844e
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_sub__f29ebb1ea461
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_mul__929a280bcbab
import Theorems.Thm_Formalism_L2_KerInert_VC_intPS_wSer
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intMv_of_intPS
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_intMv


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
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
variable {R'}
namespace Formalism.L2.KerInert.VC
theorem _root_.solution (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R') : IntPS R' (phi W C) := by
  have hw := intPS_wSer R' hW
  have hden : IntPS R' (den W C) :=
    intPS_add' R' (intPS_add' R' (intPS_C' R' R'.one_mem) (intPS_mul' R' (intPS_C' R' hs) (intPS_X' R')))
      (intPS_mul' R' (intPS_C' R' (R'.sub_mem ht (R'.mul_mem hs hr))) hw)
  have hv : IntPS R' (vv W C) :=
    Pts.intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_of_mul_eq_one (Pts.intMv_of_intPS hden) (den_cc W C) (den_mul_vv W C))
  exact intPS_mul' R' (intPS_mul' R' (intPS_C' R' hu) (intPS_sub' R' (intPS_X' R') (intPS_mul' R' (intPS_C' R' hr) hw))) hv
end Formalism.L2.KerInert.VC
