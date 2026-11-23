-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.UmUl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:19.690079+00:00
-- url     : https://prove2.me/submissions/fbf825f9-959c-4d1d-af02-3e0cc3733ebb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_per_l

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
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (hP : P.OK) (u : ℂ) :
    Um P u * Ul P u - Ul P u * Um P u =
      kap P fun π => ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
        (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by
  have e1 : Um P u * Ul P u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      kap P (bb P u l) * star (SS P l) * (kap P (bb P u j) * SS P j) := Finset.sum_mul_sum _ _ _ _
  have e2 : Ul P u * Um P u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      kap P (bb P u j) * SS P j * (kap P (bb P u l) * star (SS P l)) :=
    (Finset.sum_mul_sum _ _ _ _).trans Finset.sum_comm
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (per_l hSh hR hNorm hMix P hP u), ← map_sum]
  exact congrArg (kap P) (funext fun π => Finset.sum_apply _ _ _)
end Formalism.FourierDecayAlt.P.Mx7
