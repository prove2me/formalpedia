-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.rhoXY_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:45.657817+00:00
-- url     : https://prove2.me/submissions/51d7e906-247d-4302-b24f-cad1bd677793

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_strict
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_xOf_redOf
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
    rhoXY m D 0 (fun _ => z, y) = z :=
  (reduced_phase_critical_points m z D (sm m (fun _ => z, y)) (rm m (fun _ => z, y)) (Xm m (fun _ => z, y))
    (Bm m (fun _ => z, y)) hz hzD (Xm_strict m _) (fun k => WeakApproximationGL.xOf_redOf m (fun _ => z, y) k)).1
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
