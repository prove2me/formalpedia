-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.kppO_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:26.112881+00:00
-- url     : https://prove2.me/submissions/0a74b23e-4f4c-458d-8273-c7690fc30cb5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_gpUni
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_isNU_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isNU_iff


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
theorem _root_.solution {j : Matrix (Idx r k) (Idx r k) o} (h : KppO j) : KppO j⁻¹ := by
  refine ⟨Matrix.isUnit_nonsing_inv_det j h.1, ?_⟩
  rw [S3x1.isNU_iff]
  refine S3x1.par_rinv S3x1.gpUni ((S3x1.isNU_iff _).1 h.2) ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h.1, Matrix.map_one _ (map_zero _) (map_one _)]
end Formalism.FourierDecayAlt.P.FrameLevelIndices
