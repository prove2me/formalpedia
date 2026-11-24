-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.restrictThirdZero_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:15.353902+00:00
-- url     : https://prove2.me/submissions/8e3e7616-fffd-4202-abbd-e3845f037349

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_hasSubst_restrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_hasSubst_sh
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
private theorem subst_fin_three_sub {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f - g) = subst a f - subst a g := by
  exact subst_sub ha f g
end Formalism.L2.Th1.B.Wr
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution (h : MvPowerSeries (Fin 3) K) : ev3 (sh h) = ev3 h := by
  unfold Formalism.L2.Th1.B.ev3 sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_restrictThirdZero]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hasSubst_restrictThirdZero, subst_fin_three_sub hasSubst_restrictThirdZero]
end Formalism.L2.Th1.B.Wr
