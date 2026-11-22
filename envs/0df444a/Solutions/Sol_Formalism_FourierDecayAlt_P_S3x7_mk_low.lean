-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.mk_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:34.146007+00:00
-- url     : https://prove2.me/submissions/499910fc-ceb1-4315-86c2-de4d309f41ae

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
theorem _root_.solution {r : ℕ} {L : Matrix (Fin r) (Fin r) A} (h : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : IsLowUni L :=
  ⟨fun i j hij => h i j (by simpa using hij), h1⟩
end Formalism.FourierDecayAlt.P.S3x7
