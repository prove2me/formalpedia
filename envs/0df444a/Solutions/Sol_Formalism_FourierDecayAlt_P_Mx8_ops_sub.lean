-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.ops_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:47.976708+00:00
-- url     : https://prove2.me/submissions/e2b32073-1db9-4dac-a90f-d0115b857a1a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_star_generators


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
theorem _root_.solution (P : Par) (i : Fin P.r) : ∀ x ∈ ops (siteA P i),
    x ∈ ({pA P i, cA P i, ciA P i, -pbA P i, cbA P i, cbiA P i} : Set (A P)) := by
  intro x hx
  obtain ⟨hs, -⟩ := star_generators P
  obtain ⟨h1, h2, h3⟩ := hs i
  rcases (hx : x ∈ hol (siteA P i) ∨ star x ∈ hol (siteA P i)) with hx | hx
  · simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  · simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have e : x = star (star x) := (star_star x).symm
    rcases hx with hx | hx | hx <;> rw [e, hx] <;> simp [h1, h2, h3]
end Formalism.FourierDecayAlt.P.Mx8
