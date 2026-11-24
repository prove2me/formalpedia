-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sq.mul_dz_fLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:19.10266+00:00
-- url     : https://prove2.me/submissions/1fc82215-a42b-4673-a2e7-8ce9af1c16b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Theorems.Thm_Formalism_L2_Th1_B_mul_pd_fLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
private theorem pd_unit_eq_dz (f : PowerSeries K) : pd () f = dz f := by
  ext n
  rw [PowerSeries.coeff_derivative,
    PowerSeries.coeff_def (s := Finsupp.single () n) (by simp), MvPowerSeries.coeff_pderiv,
    PowerSeries.coeff_def (s := Finsupp.single () (n + 1)) (by simp), ← Finsupp.single_add,
    Finsupp.single_eq_same]
end Formalism.L2.Th1.B.Sq
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Sq
theorem _root_.solution {g : PowerSeries K} (hg : constantCoeff g = 1) : g * dz (fLog g) = dz g := by
  have h := mul_pd_fLog (ι := Unit) () (g := g) hg
  rwa [pd_unit_eq_dz, pd_unit_eq_dz] at h
end Formalism.L2.Th1.B.Sq
