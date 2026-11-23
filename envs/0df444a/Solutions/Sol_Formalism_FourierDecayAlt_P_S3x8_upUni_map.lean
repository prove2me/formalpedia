-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.upUni_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:34.965844+00:00
-- url     : https://prove2.me/submissions/28a0dac4-bdb6-4163-bdfb-e7933e09df33

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
theorem _root_.solution (f : A →+* F) {r : ℕ} {x : Matrix (Fin r) (Fin r) A} (h : IsUpUni x) :
    IsUpUni (x.map f) :=
  ⟨fun i j hij => by simp [h.1 hij], fun a => by simp [h.2 a]⟩
end Formalism.FourierDecayAlt.P.S3x8
