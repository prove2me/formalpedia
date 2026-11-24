-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.subst_sgStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:16.510608+00:00
-- url     : https://prove2.me/submissions/08ea730f-ce67-410b-bb25-63f08743372c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_psubst_fExp

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
theorem _root_.solution {ι : Type} (s2 : K) (P : PowerSeries K)
    {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sgStar s2 P) =
      PowerSeries.subst u (sigma P) * fExp (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [sgStar, PowerSeries.subst_mul hs, psubst_fExp hu (by simp)]
  congr 2
  rw [← PowerSeries.coe_substAlgHom hs, map_neg, map_mul, map_pow, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom hs, PowerSeries.subst_C]
end Formalism.L2.Th1.B.Fs
