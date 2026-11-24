-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.exp_Zm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:49:26.97639+00:00
-- url     : https://prove2.me/submissions/e38cf6bc-7bcc-4a4a-91ee-9ce5596515a8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (s : ℝ) : NormedSpace.exp ((s : ℂ) • Zm k r) = aDil k r (Real.exp s) := by
  unfold Zm
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, aDil_eq]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  unfold zd dg
  by_cases c1 : i.val < r
  · simp only [c1, if_true, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  · by_cases c2 : i.val ≤ r + k
    · simp [c1, c2]
    · simp only [c1, c2, if_false, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
      congr 1
      ring
end Formalism.FourierDecayAlt.P.B4
