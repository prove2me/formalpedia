-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.z_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:05.733781+00:00
-- url     : https://prove2.me/submissions/0e670b97-ec0e-41f5-b3eb-81d4e6c5656e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_gamma_family_commute_generators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_ops_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_mem_Cen
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
theorem _root_.solution (P : Par) (i : Fin P.r) : ∀ y ∈ ({zA P, zbA P, ggA P, ggiA P, nabA P, nabsA P} : Set (A P)),
    y ∈ Cen P i := by
  obtain ⟨L, hL⟩ := Mx2.levelExists P
  have key := gamma_family_commute_generators L i
  have hG := ops_G P L hL i
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩ := hL
  rw [hz, hzb, hgg, hggi, hnab, hnabs] at key
  intro y hy
  rw [mem_Cen]
  exact fun g hg => key g (hG g hg) y hy
end Formalism.FourierDecayAlt.P.Mx8
