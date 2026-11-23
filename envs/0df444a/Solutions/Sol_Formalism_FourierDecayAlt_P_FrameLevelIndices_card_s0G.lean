-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.card_s0G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:51.892004+00:00
-- url     : https://prove2.me/submissions/4b225d53-433b-430a-b9d9-3097ebeccf74

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_par_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_of_subgroupSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameLevelIndices
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices
theorem _root_.solution : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsInertiaInfiniteCyclotomic x} =
    Nat.card (S3x1.s0G : Subgroup (GL (Idx r k) A)) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.mem_pointwise_stabiliser_iff x).1 hx).1), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg
end Formalism.FourierDecayAlt.P.FrameLevelIndices
