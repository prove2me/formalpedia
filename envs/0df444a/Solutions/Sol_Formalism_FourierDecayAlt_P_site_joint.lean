-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.site_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:17.23567+00:00
-- url     : https://prove2.me/submissions/602a0b3d-d89a-489d-838d-a98884411d47

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.SiteJoint := by
  intro P L hL l Y
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  obtain ⟨hs, -⟩ := star_generators P
  obtain ⟨h1, h2, h3⟩ := hs l
  refine ⟨?_, fun hY => ?_⟩
  · simp only [LevelData.Tl, Ts, Tm, siteA, hp, hc, hci]
  · simp only [LevelData.Tvl, Ts, Tm, siteA, hpb, hcb, hcbi]
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b
    · show algebraMap ℂ (A P) Y - pbA P l = star (algebraMap ℂ (A P) Y + pA P l)
      rw [star_add, h3, ← algebraMap_star_comm, hY, sub_eq_add_neg]
    · show -cbA P l = star (-cA P l)
      rw [star_neg, h1]
    · exact h2.symm
    · exact (star_zero (A P)).symm
end Formalism.FourierDecayAlt.P
