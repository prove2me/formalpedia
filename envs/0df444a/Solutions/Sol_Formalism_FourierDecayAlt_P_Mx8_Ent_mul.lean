-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.Ent.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:35.9603+00:00
-- url     : https://prove2.me/submissions/4f41b743-86a7-4d3a-a8fe-edb1a774f147

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
variable {A : Type} [Ring A] [Algebra ℂ A] {C : Subalgebra ℂ A}
namespace Formalism.FourierDecayAlt.P.Mx8
namespace Ent
theorem _root_.solution {M N : M2 A} (hM : Ent C M) (hN : Ent C N) : Ent C (M * N) := by
  intro a b
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hM a k) (hN k b)
end Ent
end Formalism.FourierDecayAlt.P.Mx8
