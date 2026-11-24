-- Prove2me | solution 1 for Formalism.L2.Th1.B.fExp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:27.332643+00:00
-- url     : https://prove2.me/submissions/dbc99a68-fcfa-46c2-823c-69dc3cedc744

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_exp_biv
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
theorem _root_.solution {f g : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : fExp (f + g) = fExp f * fExp g := by
  have hb : MvPowerSeries.HasSubst ![f, g] :=
    hasSubst_of_forall_constantCoeff_eq_zero (fun i => by fin_cases i <;> simpa)
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h := congrArg (MvPowerSeries.subst ![f, g]) (exp_biv (K := K))
  rw [psubst_msubst _ h01 hb, MvPowerSeries.subst_mul hb, psubst_msubst _ h0 hb,
    psubst_msubst _ h1 hb] at h
  simpa [fExp, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb] using h
end Formalism.L2.Th1.B
