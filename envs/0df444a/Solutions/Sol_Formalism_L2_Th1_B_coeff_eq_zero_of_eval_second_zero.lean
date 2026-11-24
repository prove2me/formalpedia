-- Prove2me | solution 1 for Formalism.L2.Th1.B.coeff_eq_zero_of_eval_second_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:23.01094+00:00
-- url     : https://prove2.me/submissions/b1aa2931-6609-4a07-a386-bfc9d0eb4059

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_coeff_evalYZero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution {h : MvPowerSeries (Fin 2) K} (h0 : ev0 h = 0) (n : Fin 2 →₀ ℕ)
    (hn : n 1 = 0) : coeff n h = 0 := by
  have hn' : n = Finsupp.single 0 (n 0) := by
    ext a
    fin_cases a <;> simp [hn]
  rw [hn', ← coeff_evalYZero, h0, map_zero]
end Formalism.L2.Th1.B
