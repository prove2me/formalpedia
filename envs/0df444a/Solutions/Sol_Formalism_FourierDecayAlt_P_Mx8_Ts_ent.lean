-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.Ts_ent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:38.573579+00:00
-- url     : https://prove2.me/submissions/5b54d858-50c1-4f17-a6bb-c5d7fc8305f8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_sitesCommuteA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_mem_Cen

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
theorem _root_.solution (P : Par) (i j : Fin P.r) (h : i ≠ j) (Y : ℂ) : Ent (Cen P i) (Ts (siteA P j) Y) := by
  have key : ∀ y ∈ hol (siteA P j), y ∈ Cen P i := fun y hy =>
    mem_Cen.2 fun g hg => sitesCommuteA P i j h g hg y (Or.inl hy)
  exact Ent.Ts (key _ (by simp [hol])) (key _ (by simp [hol])) (key _ (by simp [hol])) Y
end Formalism.FourierDecayAlt.P.Mx8
