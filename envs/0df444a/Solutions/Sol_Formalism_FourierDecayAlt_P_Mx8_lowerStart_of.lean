-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.lowerStart_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:19.856675+00:00
-- url     : https://prove2.me/submissions/61348fa5-90ab-432f-884b-3d203994f59f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_isStart_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_isSiteA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_chainM
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_lowerCommutes

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
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (h : StartIsStart) : LowerStart := by
  intro P hP l
  have key : ∀ d i : ℕ, i + d = P.r → IsStart (QQlev P l i) (qC P) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have e : QQlev P l i = (startM P l).QQ := by
        funext Y
        rw [show i = P.r by omega]
        exact (chainM P l).1 Y
      rw [e]
      exact h P hP l
    | succ d ih =>
      intro i hi
      have hlt : i < P.r := by omega
      have e : QQlev P l i = fun Y => (Ts (siteA P ⟨i, hlt⟩) (star Y))ᴴ * QQlev P l (i + 1) Y *
          Ts (siteA P ⟨i, hlt⟩) Y := by
        funext Y
        exact (chainM P l).2 ⟨i, hlt⟩ Y
      rw [e]
      exact isStart_step _ _ _ (isSiteA P _) (lowerCommutes P l ⟨i, hlt⟩) (ih (i + 1) (by omega))
  intro i hi
  exact key (P.r - i) i (by omega)
end Formalism.FourierDecayAlt.P.Mx8
