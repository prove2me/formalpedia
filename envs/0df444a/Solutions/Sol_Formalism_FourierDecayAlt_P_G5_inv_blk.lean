-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.inv_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:44.65831+00:00
-- url     : https://prove2.me/submissions/866e16df-ff39-4f03-9891-3e99f729dad5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_mul_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_upper_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (v : UT n → ℂ) (b : Fin n → ℂ) :
    (blk (upper v) b 0 1)⁻¹ = blk (upper v)⁻¹ ((-(upper v)⁻¹) *ᵥ b) 0 1 := by
  refine Matrix.inv_eq_right_inv ?_
  rw [blk_mul_upper, upper_mul_inv, Matrix.mulVec_mulVec, Matrix.mul_neg, upper_mul_inv, Matrix.neg_mulVec,
    Matrix.one_mulVec, neg_add_cancel, blk_one]
end Formalism.FourierDecayAlt.P.G5
