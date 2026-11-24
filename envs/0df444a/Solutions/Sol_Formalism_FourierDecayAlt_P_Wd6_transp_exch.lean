-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.transp_exch
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:56.922887+00:00
-- url     : https://prove2.me/submissions/fd447143-0dce-4570-a5b9-931046b166bb

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_mul_of_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_mul_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_diag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {X T : M2 B} {b : B} (hc : ∀ i j, EC (X i j) T)
    (h : X * T * (Matrix.diagonal fun _ => b) = (Matrix.diagonal fun _ => b) * T * X) :
    Tᵀ * Xᵀ * (Matrix.diagonal fun _ => b) = (Matrix.diagonal fun _ => b) * Xᵀ * Tᵀ := by
  have hc' : ∀ i j, EC (T i j) X := fun i j k l => (hc k l i j).symm
  have h' := congrArg Matrix.transpose h
  rw [transpose_mul_diag, mul_assoc, transpose_diag_mul, transpose_mul_of_comm hc,
    transpose_mul_of_comm hc'] at h'
  rw [h', mul_assoc]
end Formalism.FourierDecayAlt.P.Wd6
