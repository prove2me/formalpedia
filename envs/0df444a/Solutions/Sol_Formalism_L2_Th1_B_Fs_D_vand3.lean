-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.D_vand3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:33.569613+00:00
-- url     : https://prove2.me/submissions/a1722a99-1840-475d-b724-59409b5e0ceb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pdX

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
theorem _root_.solution : pd 1 (vand3 K) - pd 2 (vand3 K) =
    (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      (-((MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2)) +
        (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) +
        2 * ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2))) := by
  simp only [vand3, pd, Derivation.leibniz, map_add, map_sub, smul_eq_mul, pdX]
  simp
  ring
end Formalism.L2.Th1.B.Fs
