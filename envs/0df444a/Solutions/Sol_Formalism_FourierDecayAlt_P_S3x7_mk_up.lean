-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.mk_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:38.214854+00:00
-- url     : https://prove2.me/submissions/7d977f52-fa44-40ef-a6bc-1d7f296af2f6

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
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {r : ℕ} {U : Matrix (Fin r) (Fin r) A} (h : ∀ i j, j < i → U i j = 0)
    (h1 : ∀ i, U i i = 1) : IsUpUni U :=
  ⟨fun i j hij => h i j (by simpa using hij), h1⟩
end Formalism.FourierDecayAlt.P.S3x7
