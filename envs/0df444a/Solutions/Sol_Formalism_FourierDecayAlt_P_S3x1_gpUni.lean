-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.gpUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:30.188176+00:00
-- url     : https://prove2.me/submissions/3a46ce70-0317-451d-83b8-0f6b6cb55950

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective

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
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution : GP (IsUpUni : Matrix (Fin k) (Fin k) A → Prop) where
  one := isUpUni_one A
  mul := fun a b => isUpUni_mul A a b
  inv := fun a => isUpUni_inv A a
  unit := by intro h a; rw [isUpUni_det A a]; exact isUnit_one
end Formalism.FourierDecayAlt.P.S3x1
