-- Prove2me | solution 1 for Formalism.MainNotions.J.Ex_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:57.589586+00:00
-- url     : https://prove2.me/submissions/f5f3af25-d06b-4509-b0a1-f9412e980fd1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_subst_Ex
import Theorems.Thm_Formalism_MainNotions_J_Ex_biv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.J
open MvPowerSeries
section AlgebraTools
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
private theorem hasSubst_of_finite_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, constantCoeff (c s) = 0) : HasSubst c := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hc
end AlgebraTools
section Exp
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
end Exp
section Int
variable {ι κ : Type} {K : Type} [Field K]
end Int
end Formalism.MainNotions.J
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
namespace Formalism.MainNotions.J
theorem _root_.solution {f g : MvPowerSeries ι K} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    Ex (f + g) = Ex f * Ex g := by
  have hc : HasSubst (![f, g] : Fin 2 → MvPowerSeries ι K) :=
    hasSubst_of_finite_constantCoeff_eq_zero (by intro i; fin_cases i <;> simp [hf, hg])
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have key := congrArg (subst (![f, g] : Fin 2 → MvPowerSeries ι K)) (Ex_biv (K := K))
  rw [subst_Ex hc h01, MvPowerSeries.subst_mul hc, subst_Ex hc h0, subst_Ex hc h1,
    MvPowerSeries.subst_add hc, MvPowerSeries.subst_X hc, MvPowerSeries.subst_X hc] at key
  simpa using key
end Formalism.MainNotions.J
