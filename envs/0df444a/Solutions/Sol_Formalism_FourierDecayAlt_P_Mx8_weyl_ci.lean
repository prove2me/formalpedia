-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.weyl_ci
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:52.374818+00:00
-- url     : https://prove2.me/submissions/42dc3656-220c-46a4-8c86-dfad85aee080

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
theorem _root_.solution {p c ci : A} (h : WeylRel p c ci) : p * ci = ci * p - ci := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ci * p = p * ci + ci := by
    have e := congrArg (fun x => ci * x * ci) h3
    simp only [mul_add, add_mul, ← mul_assoc, h2, one_mul] at e
    rw [mul_assoc (ci * p), h1, mul_one] at e
    exact e
  rw [key]; abel
end Formalism.FourierDecayAlt.P.Mx8
