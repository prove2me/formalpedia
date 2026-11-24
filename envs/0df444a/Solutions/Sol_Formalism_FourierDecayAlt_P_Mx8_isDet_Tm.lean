-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.isDet_Tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:57.804531+00:00
-- url     : https://prove2.me/submissions/91e6acbb-27aa-48ab-a5d8-dff68b87780e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_YangianSpanCharacter_P_transposeSymplecticShift


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
theorem _root_.solution {p c ci : A} (h : WeylRel p c ci) : IsDet (fun Y : ℂ => Tm Y p c ci) (fun _ => 1) := by
  intro Y
  refine ⟨?_, ?_⟩
  · rw [map_one, one_smul]
    exact Formalism.YangianSpanCharacter.P.transposeSymplecticShift ℂ A p c ci Y h
  · rw [map_one, one_smul]
    obtain ⟨h1, h2, h3⟩ := h
    have hc : algebraMap ℂ A Y * c = c * algebraMap ℂ A Y := Algebra.commutes _ _
    ext a b
    fin_cases a <;> fin_cases b
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, h3, hc]
      abel
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h1]
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h2]
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
end Formalism.FourierDecayAlt.P.Mx8
