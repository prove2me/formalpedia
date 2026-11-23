-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.top_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:39.367799+00:00
-- url     : https://prove2.me/submissions/c63fb12a-3220-411c-81c6-bcb57f340127

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_strict
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_sum_mul_zero_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_leading_cofactor


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
theorem _root_.solution (m : ℕ) (p : XY m) : ((-Xm m p) ^ m *ᵥ Bm m p) 0 = cof0XY m p := by
  have h := (leading_cofactor m (Xm m p) (Bm m p) (rm m p) (Xm_strict m p)).1
  rw [Cof, G6.sum_mul_zero_pow m (fun j => ((-Xm m p) ^ j *ᵥ Bm m p) 0)] at h
  rw [h, cof0XY]
  congr 1
  exact Finset.prod_congr rfl fun k _ => WeakApproximationGL.xOf_redOf m p k
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
