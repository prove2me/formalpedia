-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.lead_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:58.290174+00:00
-- url     : https://prove2.me/submissions/89a9021a-c695-4c57-bce8-b8b5cb6a44a0

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
theorem _root_.solution {r : ℕ} (M : Matrix (Fin r) (Fin r) A) : lead M r le_rfl = M.det := by
  unfold lead
  congr 1
end Formalism.FourierDecayAlt.P.S3x8
