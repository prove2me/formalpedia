-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.partialDeriv_two_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:44.016328+00:00
-- url     : https://prove2.me/submissions/0d13ba6a-a28d-4a54-8fdf-9c489c5f2204

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_cc_sh
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst

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
private theorem pderiv_X_fin_three_self (i : Fin 3) :
    MvPowerSeries.pderiv K i (X i : MvPowerSeries (Fin 3) K) = 1 := by
  simp
private theorem pderiv_X_fin_three_of_ne {i j : Fin 3} (hij : j ≠ i) :
    MvPowerSeries.pderiv K i (X j : MvPowerSeries (Fin 3) K) = 0 := by
  simp [hij]
end Formalism.L2.Th1.B.Wr
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution (h : MvPowerSeries (Fin 3) K) : pd 2 (sh h) = sh (pd 2 h) - sh (pd 1 h) := by
  unfold sh Formalism.L2.Th1.B.pd
  rw [Formalism.G.LogCR.pderiv_subst cc_sh, Fin.sum_univ_three]
  simp [pderiv_X_fin_three_self, pderiv_X_fin_three_of_ne]
  try ring
end Formalism.L2.Th1.B.Wr
