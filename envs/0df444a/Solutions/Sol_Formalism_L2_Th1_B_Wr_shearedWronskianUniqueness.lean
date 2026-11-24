-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.shearedWronskianUniqueness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:39.317896+00:00
-- url     : https://prove2.me/submissions/20661fc8-9401-4ed4-baa3-2c221dbe9556

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_wronskianUniqueness
import Theorems.Thm_Formalism_L2_Th1_B_Wr_sh_mul
import Theorems.Thm_Formalism_L2_Th1_B_Wr_sh_sub
import Theorems.Thm_Formalism_L2_Th1_B_Wr_shI_sh
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_shear
import Theorems.Thm_Formalism_L2_Th1_B_Wr_partialDeriv_two_shear

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
theorem _root_.solution : ShearLemma := by
  intro L _ _ A Bs hw hr hB
  have h1 : sh A * Formalism.L2.Th1.B.pd 2 (sh Bs) = sh Bs * Formalism.L2.Th1.B.pd 2 (sh A) := by
    rw [partialDeriv_two_shear, partialDeriv_two_shear]
    have e := congrArg sh hw
    rw [sh_mul, sh_mul, sh_sub, sh_sub] at e
    linear_combination -e
  have h2 : Formalism.L2.Th1.B.ev3 (sh A) = Formalism.L2.Th1.B.ev3 (sh Bs) := by
    rw [restrictThirdZero_shear, restrictThirdZero_shear, hr]
  have h3 : Formalism.L2.Th1.B.ev3 (sh Bs) ≠ 0 := by
    rwa [restrictThirdZero_shear]
  have h4 := wronskianUniqueness L (sh A) (sh Bs) h1 h2 h3
  calc A = shI (sh A) := (shI_sh A).symm
    _ = shI (sh Bs) := by rw [h4]
    _ = Bs := shI_sh Bs
end Formalism.L2.Th1.B.Wr
