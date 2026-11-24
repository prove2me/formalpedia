-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.ops_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:06:58.360676+00:00
-- url     : https://prove2.me/submissions/0be4b32d-335c-48ec-bc09-c2cd84975d8b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_ops_sub

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
theorem _root_.solution (P : Par) (i : Fin P.r) : ∀ x ∈ ops (siteA P i), ∃ w, x = sc P w := by
  intro x hx
  have := ops_sub P i x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pP i, rfl⟩
  · exact ⟨cP i, rfl⟩
  · exact ⟨ciP i, rfl⟩
  · refine ⟨-pbP i, ?_⟩
    unfold pbA sc
    rw [map_neg]
  · exact ⟨cbP i, rfl⟩
  · exact ⟨cbiP i, rfl⟩
end Formalism.FourierDecayAlt.P.Mx8
