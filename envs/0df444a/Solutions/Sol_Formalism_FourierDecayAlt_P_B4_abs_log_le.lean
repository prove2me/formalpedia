-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.abs_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:55.505917+00:00
-- url     : https://prove2.me/submissions/c5d896c6-3683-48f6-878a-4ea70edcc89f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_abs_inv_sub_one

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
theorem _root_.solution {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |Real.log t| ≤ 2 * |t - 1| := by
  have hpos : 0 < t := by linarith [ht.1]
  have h2 := abs_inv_sub_one ht
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hpos
    linarith [le_abs_self (t⁻¹ - 1)]
  · have := Real.log_le_sub_one_of_pos hpos
    linarith [le_abs_self (t - 1), abs_nonneg (t - 1)]
end Formalism.FourierDecayAlt.P.B4
