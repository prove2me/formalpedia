-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.gExt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:35.202872+00:00
-- url     : https://prove2.me/submissions/5f7c4eba-a54f-47d0-a6ac-7c2e4f8b291d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_strict
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rhoXY_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_differentiable_cofXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_leading_cofactor_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_at_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_limit_coordinates_xy
import Theorems.Thm_Formalism_FourierDecayAlt_P_reduced_phase_critical_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (m : ℕ) (D z : ℂ) (y : UT (m + 2) → ℂ) (hz : z ≠ 0) (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    gExt m D 0 (fun _ => z, y) = superSum (strictUpper y) / z := by
  set p : XY m := (fun _ => z, y) with hp
  have hprod : ∏ k, p.1 k ≠ 0 := by simp [hp, hz]
  have hc0 : cofXY m 0 p ≠ 0 := by rw [cofXY_at_zero]; exact leading_cofactor_ne_zero m p hprod
  have h1 := (reduced_phase_critical_points m z D (sm m p) (rm m p) (Xm m p) (Bm m p) hz hzD (Xm_strict m _)
    (fun k => WeakApproximationGL.xOf_redOf m p k)).2
  have hL : wMat (m + 2) * Mcoord 0 (Xm m p) (Bm m p) (Fin.cons z (rm m p)) (sm m p) =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y := limit_coordinates_xy m z y
  have hS : superSum (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y) =
      superSum (strictUpper y) := by
    unfold superSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
    simp [this]
  rw [hL, hS] at h1
  have hg : DifferentiableAt ℂ (fun t => gExt m D t p) 0 := by
    unfold gExt r1XY cof1XY
    refine DifferentiableAt.mul (DifferentiableAt.mul (by fun_prop) ?_) (by fun_prop)
    exact (differentiable_cofXY m p 0).inv hc0
  have h2 : HasDerivAt (fun t => (-1) ^ (m + 3) * D / ∏ k, p.1 k + t * gExt m D t p) (gExt m D 0 p) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt).const_add ((-1) ^ (m + 3) * D / ∏ k, p.1 k)
    simpa using this
  have h3 : HasDerivAt (fun t => rhoXY m D t p) (gExt m D 0 p) 0 := by
    refine h2.congr_of_eventuallyEq ?_
    have hev : ∀ᶠ t in nhds (0 : ℂ), cofXY m t p ≠ 0 :=
      (differentiable_cofXY m p).continuous.continuousAt.eventually_ne hc0
    filter_upwards [hev] with t ht
    exact rhoXY_ext m D t p ht hprod
  exact h3.unique h1
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
