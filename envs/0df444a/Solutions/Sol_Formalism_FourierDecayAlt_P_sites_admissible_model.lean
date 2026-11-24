-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sites_admissible_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:39:46.338227+00:00
-- url     : https://prove2.me/submissions/fd855388-03ed-442e-a040-5efdd7b6132c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_isSiteA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_sitesCommuteA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_start_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_commutes_of_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_mem_sitesFrom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.SitesOKM := by
  intro P l
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := Mx8.mem_sitesFrom P 0 σ hσ
    exact ⟨Mx8.isSiteA P j, Mx8.commutes_of_ent P j _ (Mx8.start_ent P l j)⟩
  · unfold sitesFrom
    rw [List.drop_zero, List.pairwise_reverse, List.pairwise_ofFn]
    intro i j hij
    exact Mx8.sitesCommuteA P j i (ne_of_gt hij)
end Formalism.FourierDecayAlt.P
