-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.isRTT_Tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:59.475323+00:00
-- url     : https://prove2.me/submissions/9a8533c0-af1e-4724-b684-e6bde68e9738

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_YangianSpanCharacter_P_rttRelation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8
variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution {p c ci : A} (h : WeylRel p c ci) : IsRTT (fun Y : ℂ => Tm Y p c ci) :=
  fun Y Y' => Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' h
end Formalism.FourierDecayAlt.P.Mx8
