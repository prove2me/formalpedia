-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.sitesCommuteA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:17.441932+00:00
-- url     : https://prove2.me/submissions/4ac36b6e-9bc6-489d-9a5f-f73f9b63def1

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_G_comm_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_ops_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levelExists


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
theorem _root_.solution (P : Par) (i j : Fin P.r) (h : i ≠ j) : SitesCommute (siteA P i) (siteA P j) := by
  obtain ⟨L, hL⟩ := Mx2.levelExists P
  exact fun x hx y hy => G_comm_ne L i j h x (ops_G P L hL i x hx) y (ops_G P L hL j y hy)
end Formalism.FourierDecayAlt.P.Mx8
