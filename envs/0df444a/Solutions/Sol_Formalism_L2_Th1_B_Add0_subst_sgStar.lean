-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.subst_sgStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:13.647137+00:00
-- url     : https://prove2.me/submissions/60d8ae69-6361-4548-a742-3b8e6417ab7d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_fExp

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
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution (h3 : ExpLogSubst) (s2 : K) (P : PowerSeries K)
    {u : MvPowerSeries (Fin 2) K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sgStar s2 P) =
      PowerSeries.subst u (sigma P) * fExp (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) := by
  have ha : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold sgStar
  have hg : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
    simp
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom]
  congr 1
  rw [subst_fExp h3 hu hg]
  congr 1
  rw [← PowerSeries.coe_substAlgHom ha, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha, PowerSeries.subst_C]
end Formalism.L2.Th1.B.Add0
