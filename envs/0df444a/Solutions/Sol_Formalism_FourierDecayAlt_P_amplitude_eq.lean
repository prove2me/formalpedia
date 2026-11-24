-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.amplitude_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:50.430681+00:00
-- url     : https://prove2.me/submissions/5ade2b39-38f5-47dd-943d-c4752bdf2212

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.AmpEq := by
  intro m β D t ht V _ _ Φ p
  have hx := xOf_redOf m p
  unfold amp redIntegrand
  rw [smul_smul, ← mul_assoc, ← (additive_character_psi β _ _).1]
  congr 3
  unfold gRem g0 rhoXY
  simp only [hx]
  field_simp
  ring
end Formalism.FourierDecayAlt.P
