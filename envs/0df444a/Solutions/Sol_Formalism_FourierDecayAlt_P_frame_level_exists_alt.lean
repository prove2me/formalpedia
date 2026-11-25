-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_level_exists_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:40.629904+00:00
-- url     : https://prove2.me/submissions/5b08d2ba-6ba9-4457-a678-6a00ebea044e

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_pointwise_stabiliser_is_subgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.FrameLevelExists :=
  by
  intro o _ _ r k
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.S3x1.pointwise_stabiliser_is_subgroup (A := IsLocalRing.ResidueField o) (r := r) (k := k)
  refine ⟨⟨B.comap (Formalism.FourierDecayAlt.S3.red o (Formalism.FourierDecayAlt.S3.Idx r k)), fun x => ?_⟩⟩
  rw [Subgroup.mem_comap, hB]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨g, hg, he⟩
    rwa [Units.ext he] at hg
end Formalism.FourierDecayAlt.P
