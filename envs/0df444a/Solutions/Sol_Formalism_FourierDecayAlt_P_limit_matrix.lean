-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.limit_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:34.93995+00:00
-- url     : https://prove2.me/submissions/fcd20a0e-9fdb-4949-8c94-3be994d937fa

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_strictUpper_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_superSum_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.LimitMatrix := by
  intro n z hz y
  constructor
  · rw [ptLong, upper, strictUpper_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
  · rw [upper, superSum_one_add, strictUpper_smul]
    simp [superSum, Finset.mul_sum, div_eq_inv_mul]
end Formalism.FourierDecayAlt.P
