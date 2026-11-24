-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.QQlev_ent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:39:45.350767+00:00
-- url     : https://prove2.me/submissions/1344d6cf-dd27-4167-afab-7bb1badc8fb4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_star_mem_Cen
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_start_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ts_ent
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (P : Par) (l : ℕ) (i : Fin P.r) (Y : ℂ) : Ent (Cen P i) (QQlev P l (i + 1) Y) := by
  have hT : ∀ Z : ℂ, Ent (Cen P i) (((sitesFrom P (i + 1)).map fun σ => Ts σ Z).prod) := by
    intro Z
    refine Ent.prod fun M hM => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hM
    obtain ⟨j, hj, rfl⟩ := mem_sitesFrom P _ σ hσ
    refine Ts_ent P i j ?_ Z
    intro e
    rw [e] at hj
    omega
  refine Ent.mul (Ent.mul ?_ (start_ent P l i Y)) (hT Y)
  intro a b
  rw [Matrix.conjTranspose_apply]
  exact star_mem_Cen (hT (star Y) b a)
end Formalism.FourierDecayAlt.P.Mx8
