-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.kppO_hEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:52.485026+00:00
-- url     : https://prove2.me/submissions/799de1e9-7128-4d9f-9fa5-e9a12b187281

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_gpOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_isN_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_hEmb_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_hEmb
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_map


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
theorem _root_.solution {h : Matrix (Fin k) (Fin k) o} (hd : IsUnit h.det)
    (hu : IsUpUni (h.map (IsLocalRing.residue o))) : KppO (hEmb r h) := by
  refine ⟨by rw [S3x3.det_hEmb]; exact hd, ?_⟩
  exact ⟨1, _, (S3x1.isN_iff _).2 (S3x1.par_one S3x1.gpOne), ⟨_, hu, rfl⟩, by
    rw [S3x3.hEmb_map, Matrix.one_mul]⟩
end Formalism.FourierDecayAlt.P.FrameLevelIndices
