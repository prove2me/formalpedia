-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.per_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:19.236891+00:00
-- url     : https://prove2.me/submissions/009f1965-ff2e-4663-b848-82f31c9d5d46

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_rho_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commutator_four_commuting
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commutator_expansion_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_shS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr


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
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (hP : P.OK) (u : ℂ)
    (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ j ∈ Icc 1 (P.k - 1), kap P (bb P u l) * star (SS P l) * (kap P (bb P u j) * SS P j) -
      ∑ j ∈ Icc 1 (P.k - 1), kap P (bb P u j) * SS P j * (kap P (bb P u l) * star (SS P l)) =
    kap P fun π => (Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
      (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l]
  · have h1 : star (SS P l) * kap P (bb P u l) = (kap P fun π => (u + rho P π l + 1)⁻¹) * star (SS P l) :=
      shS hSh P l _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ))⁻¹ = (u + rho P π l + 1)⁻¹
        rw [rho_up hR P l hl π π' hU]; push_cast; rw [add_assoc])
    have h2 : SS P l * kap P (bb P u l) = (kap P fun π => (u + rho P π l - 1)⁻¹) * SS P l :=
      (hSh P l _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ) - 1)⁻¹ = (u + (rho P π l : ℂ))⁻¹
        rw [rho_up hR P l hl π π' hU]; push_cast; congr 1; ring)).symm
    rw [commutator_expansion_identity _ _ _ _ _ _ _ h1 h2 (hNorm P hP l hl).1 (hNorm P hP l hl).2, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, ← map_sub]
    refine congrArg (kap P) (funext fun π => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply, bb]
    ring
  · intro j hj hjl
    have h1 : star (SS P l) * kap P (bb P u j) = kap P (bb P u j) * star (SS P l) :=
      shS hSh P l _ _ (fun π π' hU => by
        show (u + (rho P π' j : ℂ))⁻¹ = (u + (rho P π j : ℂ))⁻¹
        rw [hR P l π π' hU j hj, if_neg hjl, add_zero])
    have h2 : SS P j * kap P (bb P u l) = kap P (bb P u l) * SS P j :=
      (hSh P j _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ))⁻¹ = (u + (rho P π l : ℂ))⁻¹
        rw [hR P j π π' hU l hl, if_neg (Ne.symm hjl), add_zero])).symm
    exact commutator_four_commuting _ _ _ _ h1 h2 (kap_comm_kap P _ _).eq (hMix P hP l hl j hj hjl)
  · intro h; exact absurd hl h
end Formalism.FourierDecayAlt.P.Mx7
