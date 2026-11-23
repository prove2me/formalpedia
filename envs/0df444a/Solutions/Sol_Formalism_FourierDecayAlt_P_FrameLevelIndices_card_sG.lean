-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.card_sG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:51.956505+00:00
-- url     : https://prove2.me/submissions/207739e9-4666-4f7f-8e77-bc84bc6e6a2b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_par_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_of_subgroupSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isS_iff


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
theorem _root_.solution : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (S3x1.parG (r := r) (S3x1.gpUnit (A := A) (k := k))) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.isS_iff x).1 hx)),
      (S3x1.isS_iff x).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact (S3x1.isS_iff _).2 hg
end Formalism.FourierDecayAlt.P.FrameLevelIndices
