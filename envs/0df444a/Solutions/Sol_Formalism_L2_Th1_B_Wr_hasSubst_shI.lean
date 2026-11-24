-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.hasSubst_shI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:55.273826+00:00
-- url     : https://prove2.me/submissions/9079ecf2-3957-43d2-ae46-33a5e4022bd6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_cc_shI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
private theorem hasSubst_fin_three_of_constantCoeff_eq_zero {a : Fin 3 → MvPowerSeries (Fin 3) K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  exact hasSubst_of_constantCoeff_zero ha
end Formalism.L2.Th1.B.Wr
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_shI
end Formalism.L2.Th1.B.Wr
