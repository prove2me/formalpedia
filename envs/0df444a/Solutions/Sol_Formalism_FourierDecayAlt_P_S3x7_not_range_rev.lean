-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.not_range_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:03.383844+00:00
-- url     : https://prove2.me/submissions/5b515754-6ce0-4515-9af4-293dd79bab33

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
theorem _root_.solution {l r : ℕ} (hl : l ≤ r) {k : Fin r}
    (hk : k ∉ Set.range (fun i : Fin l => (Fin.castLE hl i).rev)) : k.val + l < r := by
  by_contra hlt
  refine hk ⟨⟨r - 1 - k.val, by have := k.isLt; omega⟩, Fin.ext ?_⟩
  have := k.isLt
  simp only [Fin.val_rev, Fin.val_castLE]
  omega
end Formalism.FourierDecayAlt.P.S3x7
