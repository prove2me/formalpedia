-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.qQDet_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:30.143638+00:00
-- url     : https://prove2.me/submissions/8d8e4125-e381-43bb-b4b9-f61c94b260e7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isSymplectic_of_eight_relations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_det8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal) :
    QQDet := by
  intro P hP Y
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := det8 hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P hP Y
  exact isSymplectic_of_eight_relations _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8
end Formalism.FourierDecayAlt.P.Mx7
