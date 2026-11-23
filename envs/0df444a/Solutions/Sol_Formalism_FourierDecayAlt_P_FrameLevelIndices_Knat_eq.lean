-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.Knat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:51.475169+00:00
-- url     : https://prove2.me/submissions/be460095-4163-4014-a179-7f86f132e38f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
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
variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices
theorem _root_.solution (L : Levels o r k) :
    L.Knat = (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))).comap
      (red o (Idx r k)) := by
  ext x
  rw [L.mem_Knat, Subgroup.mem_comap, S3x1.isS_iff]
  rfl
end Formalism.FourierDecayAlt.P.FrameLevelIndices
