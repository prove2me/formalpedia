-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.lead_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:59.869043+00:00
-- url     : https://prove2.me/submissions/52ff2078-36b2-441d-912f-b869c9447301

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
theorem _root_.solution {r : ℕ} (d : Fin r → A) (l : ℕ) (hl : l ≤ r) :
    lead (Matrix.diagonal d) l hl = ∏ i : Fin l, d (Fin.castLE hl i) := by
  unfold lead
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl
end Formalism.FourierDecayAlt.P.S3x7
