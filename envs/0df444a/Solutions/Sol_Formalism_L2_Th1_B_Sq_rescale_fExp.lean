-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sq.rescale_fExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:20.328301+00:00
-- url     : https://prove2.me/submissions/2557fa8e-b111-4450-91fb-7d84f9cad06c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Theorems.Thm_Formalism_L2_Th1_B_subst_fExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Sq
theorem _root_.solution (a : K) {f : PowerSeries K} (hf : constantCoeff f = 0) :
    rescale a (fExp f) = fExp (rescale a f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  have hφ : ∀ _ : Unit, MvPowerSeries.constantCoeff (a • (PowerSeries.X : PowerSeries K)) = 0 := by
    intro _
    show PowerSeries.constantCoeff (a • (PowerSeries.X : PowerSeries K)) = 0
    rw [PowerSeries.smul_eq_C_mul]
    simp
  exact subst_fExp (φ := fun _ => (a • PowerSeries.X : PowerSeries K)) hφ hf
end Formalism.L2.Th1.B.Sq
