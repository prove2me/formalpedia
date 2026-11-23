-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.cm_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:55.001108+00:00
-- url     : https://prove2.me/submissions/daf463ce-6cee-4517-8c4d-522d087eb5c8

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {B : Type} [CommRing B] (f : A →+* B) (X : Matrix (Fin r) (Fin r) A) (l : ℕ)
    (hl : l ≤ r) : f (cm X l hl) = cm (X.map f) l hl := by
  unfold cm
  rw [RingHom.map_det]
  rfl
end Formalism.FourierDecayAlt.P.S3x7
