-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.kronecker_E1_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:51:02.109653+00:00
-- url     : https://prove2.me/submissions/c61b091e-ac57-4ad0-a186-be63eccc718c

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
theorem _root_.solution (s : ℂ) (M : M2 A) : E1 (s • M) = s • E1 M := by
  ext ik jl
  simp only [E1, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Mx8
