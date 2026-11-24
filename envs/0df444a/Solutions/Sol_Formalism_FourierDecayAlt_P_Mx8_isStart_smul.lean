-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.isStart_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:07:54.964705+00:00
-- url     : https://prove2.me/submissions/52c4207e-e0b6-45f4-a541-f4d2aab78a33

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_kronecker_E1_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_eval_two_smul

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
theorem _root_.solution (QQ : ℂ → M2 A) (q : ℂ → ℂ) (s : ℂ) (hs : s * s = 1) (hs' : star s = s)
    (h : IsStart QQ q) : IsStart (fun Y => s • QQ Y) q := by
  refine ⟨fun Y hY => ?_, fun Y Y' => ?_, fun Y => ?_, h.q_real⟩
  · rw [Matrix.conjTranspose_smul, hs', h.herm Y hY]
  · have := h.rtt Y Y'
    simp only [kronecker_E1_smul, eval_two_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]
    exact this
  · have := h.det Y
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]
    exact this
end Formalism.FourierDecayAlt.P.Mx8
