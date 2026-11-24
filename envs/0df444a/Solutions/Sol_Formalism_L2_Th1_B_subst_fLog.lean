-- Prove2me | solution 1 for Formalism.L2.Th1.B.subst_fLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:21:59.566366+00:00
-- url     : https://prove2.me/submissions/b5ff5b27-e3b4-4adf-bbb6-c24874a9229c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_psubst_msubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B
open PowerSeries
section One
variable {K : Type} [Field K] [CharZero K]
private theorem hasSubst_of_forall_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero h
end One
section Rules
variable {K : Type} [Field K] [CharZero K] {ι : Type}
end Rules
end Formalism.L2.Th1.B
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {κ : Type} [Finite ι] {φ : ι → MvPowerSeries κ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) :
    MvPowerSeries.subst φ (fLog g) = fLog (MvPowerSeries.subst φ g) := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hφ' : MvPowerSeries.HasSubst φ := hasSubst_of_forall_constantCoeff_eq_zero hφ
  unfold fLog
  rw [psubst_msubst _ hg1 hφ', ← MvPowerSeries.coe_substAlgHom hφ', map_sub, map_one]
end Formalism.L2.Th1.B
