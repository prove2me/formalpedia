-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.mem_sitesFrom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:46.145042+00:00
-- url     : https://prove2.me/submissions/1bd40305-51ca-47a3-be6d-efe7ce478903

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
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (P : Par) (n : ℕ) (σ : Site (A P)) (h : σ ∈ sitesFrom P n) :
    ∃ j : Fin P.r, n ≤ j ∧ σ = siteA P j := by
  unfold sitesFrom at h
  rw [List.mem_reverse, List.mem_iff_getElem] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [List.length_drop, List.length_ofFn] at hk
  refine ⟨⟨n + k, by omega⟩, by simp, ?_⟩
  simp [List.getElem_drop, List.getElem_ofFn]
end Formalism.FourierDecayAlt.P.Mx8
