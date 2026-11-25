-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.concrete_sizes_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:25.16449+00:00
-- url     : https://prove2.me/submissions/1e5a80d6-07c8-4e38-ad57-a68efe19c359

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.SizesConcreteOfParts := by
  intro hLSJ hIS hBox hLG hIM hNI hDF hFP hX hILS hMk
  obtain ⟨C₁, hC₁, h⟩ := hILS hLSJ hIS hBox hLG hIM hNI hDF hFP hX
  refine ⟨C₁, hC₁, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S Kr hK0 Th e Θ hU hg1 hg2 hCA hlen hΘ hgr
  have hI := hMk E Wp Wq S Kr hK0 Th e
  obtain ⟨h1, h2⟩ := h E _ (S.mkData Kr hK0 Th e) S.pl S.G S.CA S.de S.de' S.T S.T' S.l Θ hU hI hg1 hg2
    hCA hlen hΘ hgr
  refine ⟨h1, ?_⟩
  have hK : (S.mkData Kr hK0 Th e).K = 5 := hI.2.1
  rw [hK] at h2
  exact h2
end Formalism.FourierDecayAlt.P
