-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.coeff_restrictThirdZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:20.65139+00:00
-- url     : https://prove2.me/submissions/885717c5-30dc-4071-8495-440ea5e9b990

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_eq_rescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution (h : MvPowerSeries (Fin 3) K) (n : Fin 3 →₀ ℕ) (hn : n 2 = 0) :
    coeff n (ev3 h) = coeff n h := by
  rw [restrictThirdZero_eq_rescale]
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp [hn]
end Formalism.L2.Th1.B.Wr
