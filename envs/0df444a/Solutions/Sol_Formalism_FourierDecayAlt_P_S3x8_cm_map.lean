-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.cm_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:20.26293+00:00
-- url     : https://prove2.me/submissions/cd287395-d532-4fe0-9d76-346869b1e29c

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
theorem _root_.solution (f : A →+* F) {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) :
    cm (X.map f) l hl = f (cm X l hl) := by
  unfold cm
  rw [RingHom.map_det]
  rfl
end Formalism.FourierDecayAlt.P.S3x8
