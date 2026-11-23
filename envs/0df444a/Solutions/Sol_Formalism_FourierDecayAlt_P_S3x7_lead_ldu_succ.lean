-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.lead_ldu_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:07.633299+00:00
-- url     : https://prove2.me/submissions/b4904bfc-251e-4da7-9ee7-7b62adf29e7f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_ldu

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
    (hU : IsUpUni U) (l : ℕ) (hl : l < r) :
    lead (L * Matrix.diagonal d * U) (l + 1) hl = d ⟨l, hl⟩ * lead (L * Matrix.diagonal d * U) l hl.le := by
  rw [lead_ldu d hL hU, lead_ldu d hL hU, Fin.prod_univ_castSucc, mul_comm]
  rfl
end Formalism.FourierDecayAlt.P.S3x7
