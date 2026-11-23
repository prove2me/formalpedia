-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.pderiv_series_at_variable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:26.396671+00:00
-- url     : https://prove2.me/submissions/fddfe615-7673-411b-afb3-8e209f144147

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
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
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Add0
section
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
private theorem coeff_at1_fin_two_eq_ite (x : Fin 2) (f : PowerSeries K) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (at1 x f : A2) = if d = Finsupp.single x (d x) then PowerSeries.coeff (d x) f else 0 := by
  classical
  unfold at1
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X x)]
  simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (d x) (fun n hn => by
      rw [if_neg]
      intro h'
      apply hn
      have := congrArg (fun e => e x) h'
      simp at this
      exact this.symm), if_pos h]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro n
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp
end
end Add0
open Add0
namespace Add0
section
variable {K : Type} [Field K] [CharZero K]
end
end Add0
end Formalism.L2.Th1.B
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution (i x : Fin 2) (f : PowerSeries K) :
    pd i (at1 x f : A2) = at1 x (dz f) * pd i (MvPowerSeries.X x : A2) := by
  classical
  ext d
  rw [MvPowerSeries.coeff_pderiv, coeff_at1_fin_two_eq_ite]
  by_cases hix : i = x
  · subst hix
    rw [show pd i (MvPowerSeries.X i : A2) = 1 from MvPowerSeries.pderiv_X_self, mul_one, coeff_at1_fin_two_eq_ite,
      PowerSeries.coeff_derivative]
    by_cases hd : d = Finsupp.single i (d i)
    · have h2 : d + Finsupp.single i 1 = Finsupp.single i ((d + Finsupp.single i 1 : Fin 2 →₀ ℕ) i) := by
        conv_lhs => rw [hd]
        simp
      rw [if_pos h2, if_pos hd, Finsupp.add_apply, Finsupp.single_eq_same]
    · have h2 : ¬ d + Finsupp.single i 1 = Finsupp.single i ((d + Finsupp.single i 1 : Fin 2 →₀ ℕ) i) := by
        intro h'
        apply hd
        ext j
        have := congrArg (fun e => e j) h'
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Finsupp.single_apply, Ne.symm hj] at this ⊢
          exact this
      rw [if_neg h2, if_neg hd, zero_mul]
  · rw [show pd i (MvPowerSeries.X x : A2) = 0 from MvPowerSeries.pderiv_X_of_ne (Ne.symm hix), mul_zero,
      map_zero]
    have h2 : ¬ d + Finsupp.single i 1 = Finsupp.single x ((d + Finsupp.single i 1 : Fin 2 →₀ ℕ) x) := by
      intro h'
      have := congrArg (fun e => e i) h'
      simp [Finsupp.single_apply, Ne.symm hix] at this
    rw [if_neg h2, zero_mul]
end Formalism.L2.Th1.B.Add0
