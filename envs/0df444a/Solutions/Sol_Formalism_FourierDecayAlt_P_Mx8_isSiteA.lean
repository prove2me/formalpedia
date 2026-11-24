-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.isSiteA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:42.881025+00:00
-- url     : https://prove2.me/submissions/8c0e8058-a502-48d2-8162-e2c771c06b2c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_hol_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levelExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_p_c
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
theorem _root_.solution (P : Par) (i : Fin P.r) : IsSite (siteA P i) := by
  obtain ⟨L, hL⟩ := Mx2.levelExists P
  obtain ⟨hs, -⟩ := star_generators P
  obtain ⟨h1, h2, h3⟩ := hs i
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := L.c_ci i; rwa [hc, hci] at this
  · have := L.ci_c i; rwa [hc, hci] at this
  · have := L.p_c i i; rwa [if_pos rfl, hp, hc] at this
  · have key := hol_comm L i
    rw [hp, hpb, hc, hci, hcb, hcbi] at key
    intro x hx y hy
    refine key x hx (star y) ?_
    simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> simp [h1, h2, h3]
end Formalism.FourierDecayAlt.P.Mx8
