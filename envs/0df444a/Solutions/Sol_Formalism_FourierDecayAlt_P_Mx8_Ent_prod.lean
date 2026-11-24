-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.Ent.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:06:58.253804+00:00
-- url     : https://prove2.me/submissions/166d4f29-e139-42fa-977f-31cd7a12a5f6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_one

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
variable {A : Type} [Ring A] [Algebra ℂ A] {C : Subalgebra ℂ A}
namespace Formalism.FourierDecayAlt.P.Mx8
namespace Ent
theorem _root_.solution {l : List (M2 A)} (h : ∀ M ∈ l, Ent C M) : Ent C l.prod := by
  induction l with
  | nil => rw [List.prod_nil]; exact Ent.one
  | cons M l ih =>
    rw [List.prod_cons]
    exact Ent.mul (h M (by simp)) (ih fun N hN => h N (by simp [hN]))
end Ent
end Formalism.FourierDecayAlt.P.Mx8
