-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.pointwise_stabiliser_is_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:58.239823+00:00
-- url     : https://prove2.me/submissions/547ba18b-12c7-4185-ad10-d6c8c47bbdbb

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_par_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
variable {P : Matrix (Fin k) (Fin k) A → Prop}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution : IsSubgroupSet (IsInertiaInfiniteCyclotomic (A := A) (r := r) (k := k)) := by
  refine ⟨s0G, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (par_det gpUnit ((mem_pointwise_stabiliser_iff x).1 hx).1), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg
end Formalism.FourierDecayAlt.P.S3x1
