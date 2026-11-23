-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.upUni_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:36.076922+00:00
-- url     : https://prove2.me/submissions/7bc55692-afcb-492b-ae74-6b8c3f9762cb

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
theorem _root_.solution (f : A →+* F) (hf : Function.Injective f) {r : ℕ} {x : Matrix (Fin r) (Fin r) A}
    (h : IsUpUni (x.map f)) : IsUpUni x :=
  ⟨fun i j hij => hf (by simpa using h.1 hij), fun a => hf (by simpa using h.2 a)⟩
end Formalism.FourierDecayAlt.P.S3x8
