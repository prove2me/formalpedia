-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.sh_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:16.174679+00:00
-- url     : https://prove2.me/submissions/f69ce6a1-2f8d-4624-8b2d-de63a1d903bc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
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
private theorem subst_fin_three_mul {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f * g) = subst a f * subst a g := by
  exact subst_mul ha f g
end Formalism.L2.Th1.B.Wr
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution (f g : MvPowerSeries (Fin 3) K) : sh (f * g) = sh f * sh g := by
  unfold sh
  exact subst_fin_three_mul hasSubst_sh f g
end Formalism.L2.Th1.B.Wr
