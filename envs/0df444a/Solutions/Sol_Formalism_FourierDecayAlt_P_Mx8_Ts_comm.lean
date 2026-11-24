-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.Ts_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:55.581835+00:00
-- url     : https://prove2.me/submissions/2485c28f-acaa-4ef9-b079-0a3c30db596d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators

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
theorem _root_.solution (σ : Site A) (x : A) (hp : Commute x σ.p) (hc : Commute x σ.c) (hci : Commute x σ.ci)
    (Y : ℂ) (a b : Fin 2) : Commute x (Ts σ Y a b) := by
  fin_cases a <;> fin_cases b
  · show Commute x (algebraMap ℂ A Y + σ.p)
    exact Commute.add_right (Algebra.commutes Y x).symm hp
  · show Commute x (-σ.c)
    exact hc.neg_right
  · show Commute x σ.ci
    exact hci
  · show Commute x 0
    exact Commute.zero_right x
end Formalism.FourierDecayAlt.P.Mx8
