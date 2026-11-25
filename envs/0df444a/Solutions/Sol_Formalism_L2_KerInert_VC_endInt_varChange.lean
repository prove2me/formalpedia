-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.endInt_varChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:08:57.385931+00:00
-- url     : https://prove2.me/submissions/9664d3e0-f78e-4990-ac9c-cc8b102d959b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_coeff_one
import Theorems.Thm_Formalism_L2_KerInert_VC_cc_subst0
import Theorems.Thm_Formalism_L2_KerInert_VC_mulBy_eq
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_subst__f54d4fdeff52
import Theorems.Thm_Formalism_L2_KerInert_VC_intPS_compInv
import Theorems.Thm_Formalism_L2_KerInert_VC_intPS_phi
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_compInvSpec
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



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
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (c : K) (h : EndInt R' (logSer W) (expSer W) c) : EndInt R' (logSer (C • W)) (expSer (C • W)) c := by
  unfold EndInt at h ⊢
  rw [mulBy_eq]
  have hphi := intPS_phi W hW C hu hr hs ht
  have hci := compInvSpec K (phi W C) (phi_cc W C) (by rw [phi_coeff_one]; exact Units.isUnit _)
  have hpinv := intPS_compInv R' hphi (phi_cc W C) hu' (phi_coeff_one W C) (Units.mul_inv C.u)
  have hm0 : constantCoeff (Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c) = 0 :=
    cc_subst0 (by simp [(logSpec K W).1]) (expSpec K W).1
  exact intPS_subst' R' hphi (intPS_subst' R' h hpinv hci.1) (cc_subst0 hci.1 hm0)
end Formalism.L2.KerInert.VC
