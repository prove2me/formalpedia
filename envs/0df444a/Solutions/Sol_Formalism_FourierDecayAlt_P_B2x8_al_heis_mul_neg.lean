-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_heis_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:18.407797+00:00
-- url     : https://prove2.me/submissions/7b62819e-40aa-4224-ab0e-5f769ebc9a41

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_matrix_ext_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_add_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_neg_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_neg_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_hb_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (x : HPar k r') : heis0 k r' x * heis0 k r' (-x.1, -x.2) = 1 := by
  apply matrix_ext_three_block
  intro a y b
  rw [← Matrix.mulVec_mulVec, heisenberg_three_block, heisenberg_three_block, Matrix.one_mulVec]
  dsimp only
  congr 1
  · rw [al_hb_neg, al_herm_neg_right, herm_add_left, herm_smul_left, al_herm_neg_left]
    linear_combination b * hb_add_conj x.1 x.2
  · simp
end Formalism.FourierDecayAlt.P.B2x8
