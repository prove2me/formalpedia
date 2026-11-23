-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.kppO_of_isN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:46.579568+00:00
-- url     : https://prove2.me/submissions/5e57859d-8eda-4bf1-ac80-a0cf002b3f1d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_of_isN
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isN_map


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
variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices
theorem _root_.solution {n : Matrix (Idx r k) (Idx r k) o} (hn : IsN n) : KppO n := by
  refine ⟨by rw [S3x3.det_of_isN hn]; exact isUnit_one, ?_⟩
  exact ⟨_, 1, S3x3.isN_map _ hn, ⟨1, isUpUni_one _, S3x1.hEmb_one.symm⟩, (Matrix.mul_one _).symm⟩
end Formalism.FourierDecayAlt.P.FrameLevelIndices
