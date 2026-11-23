-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.lead_ldu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:15.809387+00:00
-- url     : https://prove2.me/submissions/ca60a5c8-e56b-4b6c-9000-8cb75a82118f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_invariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_diagonal

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
theorem _root_.solution {r : ℕ} {L U : Matrix (Fin r) (Fin r) A} (d : Fin r → A) (hL : IsLowUni L)
    (hU : IsUpUni U) (l : ℕ) (hl : l ≤ r) :
    lead (L * Matrix.diagonal d * U) l hl = ∏ i : Fin l, d (Fin.castLE hl i) := by
  rw [lead_invariant hL hU, lead_diagonal]
end Formalism.FourierDecayAlt.P.S3x7
