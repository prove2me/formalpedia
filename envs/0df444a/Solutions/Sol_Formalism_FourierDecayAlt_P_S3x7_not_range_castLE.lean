-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.not_range_castLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:07.745475+00:00
-- url     : https://prove2.me/submissions/65016547-9767-407b-ac71-bbb2b91b80b0

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
theorem _root_.solution {l r : ℕ} (hl : l ≤ r) {k : Fin r} (hk : k ∉ Set.range (Fin.castLE hl)) :
    l ≤ k.val := by
  by_contra hlt
  exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
end Formalism.FourierDecayAlt.P.S3x7
