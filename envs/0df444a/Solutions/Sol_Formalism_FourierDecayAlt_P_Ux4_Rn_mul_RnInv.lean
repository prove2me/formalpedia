-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.Rn_mul_RnInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:03.552666+00:00
-- url     : https://prove2.me/submissions/a8360bc6-c159-4fee-9c68-b89db9e6c3ac

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (x : RC k j ρ) : Rn k j ρ x * RnInv x = 1 := by
  rw [Rn, RnInv, block3_mul, block3_one]
  congr 1 <;>
    simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, neg_neg, smul_zero, sub_zero, neg_zero, zero_sub] <;> abel
end Formalism.FourierDecayAlt.P.Ux4
