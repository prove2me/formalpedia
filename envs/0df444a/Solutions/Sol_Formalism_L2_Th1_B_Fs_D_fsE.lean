-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.D_fsE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:05.283856+00:00
-- url     : https://prove2.me/submissions/078aeb59-3f90-4e7e-8157-f46db805db07

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pd_three
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pderiv_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pderiv_series_at_difference_three
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pderiv_series_at_sum_three
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_series_at_variable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution (f : PowerSeries K) : pd 1 (fsE f) - pd 2 (fsE f) =
    -(evalDiffThree 0 1 (dz f) - at1 0 (dz f) + at1 1 (dz f)) +
      (evalDiffThree 0 2 (dz f) - at1 0 (dz f) + at1 2 (dz f)) +
      2 * (evalDiffThree 1 2 (dz f) - at1 1 (dz f) + at1 2 (dz f)) := by
  simp only [fsE, pd, Derivation.leibniz, map_add, map_sub, smul_eq_mul, pd_three, pderiv_series_at_variable, pderiv_series_at_difference_three,
    pderiv_series_at_sum_three]
  simp
  ring
end Formalism.L2.Th1.B.Fs
