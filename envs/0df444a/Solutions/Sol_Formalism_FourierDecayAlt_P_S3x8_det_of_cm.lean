-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.det_of_cm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:59:06.099807+00:00
-- url     : https://prove2.me/submissions/9b95f412-17b6-42c0-9b56-37d45f6c0f49

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (h : IsUnit (cm X r le_rfl)) :
    IsUnit X.det := by
  have e : cm X r le_rfl = (X.submatrix Fin.revPerm id).det := by
    unfold cm
    congr 1
  rw [e, Matrix.det_permute] at h
  exact isUnit_of_mul_isUnit_right h
end Formalism.FourierDecayAlt.P.S3x8
