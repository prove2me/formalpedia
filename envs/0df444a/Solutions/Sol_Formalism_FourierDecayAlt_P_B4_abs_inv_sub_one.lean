-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.abs_inv_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:49:24.066179+00:00
-- url     : https://prove2.me/submissions/cb4d0594-50d1-4e9c-a311-ccebdc916ec9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I

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
theorem _root_.solution {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |t⁻¹ - 1| ≤ 2 * |t - 1| := by
  have hpos : 0 < t := by linarith [ht.1]
  have e : t⁻¹ - 1 = -(t - 1) * t⁻¹ := by
    first
      | (field_simp; ring)
      | field_simp
  rw [e, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hpos), mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_mem_I ht).2 (abs_nonneg _)
end Formalism.FourierDecayAlt.P.B4
