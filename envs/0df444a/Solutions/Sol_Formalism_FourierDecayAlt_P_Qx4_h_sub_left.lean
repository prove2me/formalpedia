-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.h_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:46:15.38097+00:00
-- url     : https://prove2.me/submissions/deb58365-4d0d-4b10-96b5-03bad98ed25c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_neg_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (u u' v : Fin n → ℂ) : herm H (u - u') v = herm H u v - herm H u' v := by
  rw [sub_eq_add_neg, h_add_left, h_neg_left, sub_eq_add_neg]
end Formalism.FourierDecayAlt.P.Qx4
