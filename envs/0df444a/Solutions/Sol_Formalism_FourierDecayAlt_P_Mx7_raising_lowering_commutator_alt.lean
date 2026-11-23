-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.raising_lowering_commutator_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:17.106298+00:00
-- url     : https://prove2.me/submissions/4a4f75f5-275b-4dc5-87f2-633fc36d85cb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pf
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commutator_perturbed_product
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absFin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_mA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_raising_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_Ul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ti_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commute_m0_Ul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commute_l0_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_UmUl
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm


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
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature)
    (P : Par) (hP : P.OK) (u : ℂ) (h0 : ∀ π, xC P π (u - 1) ≠ 0) (h1 : ∀ π, xC P π u ≠ 0)
    (h2 : ∀ π, xC P π (u + 1) ≠ 0) :
    mA P u * lA P u - lA P u * mA P u =
      qC P (u - 1) • (ti P (u - 1) * ti P u) - qC P u • (ti P u * ti P (u + 1)) := by
  obtain ⟨_, _, _, _, _, _, hGGi, _, hGdef⟩ := hLF P
  obtain ⟨nz, _, _, _, _, nGi, _⟩ := hLN P
  obtain ⟨nszb, _, _, _, _, nsGi, _⟩ := hLNs P
  have czzb : Commute (zA P) (zbA P) := fn_comm P _ _ _ _
  have cGiz : Commute (ggiA P) (zA P) := fn_comm P _ _ _ _
  have cGizb : Commute (ggiA P) (zbA P) := fn_comm P _ _ _ _
  have cK : Commute (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) (ggiA P) := kap_comm_sc P _ _
  have cm : Commute (ggiA P) (Um P u) := sc_Um hSc P _ _
  have cl : Commute (ggiA P) (Ul P u) := sc_Ul hSc P _ _
  rw [mA_eq, lA_eq, commutator_perturbed_product _ _ _ _ _ (commute_m0_Ul hSc hN hLNs P u) (commute_l0_Um hSc hN hSG hLN P u) cm cl,
    UmUl hSh hR hNorm hMix P hP u, raising_constant_eq_shift, lowering_constant_eq_shift,
    absC _ _ _ _ _ _ _ _ hGGi hGdef czzb.eq cGiz.eq cGizb.eq nz nGi nszb nsGi (hCurv P), ti_mul, ti_mul,
    absFin _ _ _ _ cK, ← mul_smul_comm, ← mul_smul_comm, ← mul_sub]
  refine congrArg (fun t => ggiA P * ggiA P * t) ?_
  rw [← map_smul, ← map_smul, ← map_sub, ← map_one (kap P), ← map_smul, ← map_add, ← map_add]
  refine congrArg (kap P) (funext fun π => ?_)
  have := pf P hP π u (h0 π) (h1 π) (h2 π)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
  rw [this]; push_cast; ring
end Formalism.FourierDecayAlt.P.Mx7
