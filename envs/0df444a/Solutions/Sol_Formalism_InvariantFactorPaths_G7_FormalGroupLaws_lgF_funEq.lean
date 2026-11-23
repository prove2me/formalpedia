-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.lgF_funEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:47.258809+00:00
-- url     : https://prove2.me/submissions/78a8a782-6e9c-49eb-9014-3fcdd753dff9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace FormalGroupLaws
section Alg
variable {K : Type} [Field K]
private theorem coeff_lgF_pow_sq_pow_eq_inv_pow (p : ℕ) (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ j) (lgF K p) = ((p : K) ^ j)⁻¹ := by
  have hq : 2 ≤ p ^ 2 := by nlinarith
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (Nat.pow_right_injective hq h).symm
  · intro hj
    exfalso
    apply hj
    rw [Finset.mem_range]
    have : j < (p ^ 2) ^ j := Nat.lt_pow_self (by omega)
    omega
private theorem coeff_lgF_eq_zero_of_ne_pow_sq_pow (p n : ℕ) (h : ∀ j, n ≠ (p ^ 2) ^ j) :
    PowerSeries.coeff n (lgF K p) = 0 := by
  rw [lgF, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero (fun i _ => if_neg (h i))
end Alg
end FormalGroupLaws
open FormalGroupLaws
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) :
    lgF K p - (p : K)⁻¹ • PowerSeries.subst ((PowerSeries.X : PowerSeries K) ^ (p ^ 2)) (lgF K p) =
      PowerSeries.X := by
  have hq0 : p ^ 2 ≠ 0 := by positivity
  have hq : 2 ≤ p ^ 2 := by nlinarith
  ext n
  rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_subst_X_pow hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (p ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
      have hnd : ¬ p ^ 2 ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
      simp only [pow_zero]
      rw [if_neg hnd, coeff_one_lgF p hp]
      simp
    | succ j =>
      have hd : p ^ 2 ∣ (p ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (p ^ 2) ^ (j + 1) / p ^ 2 = (p ^ 2) ^ j := by
        rw [pow_succ, Nat.mul_div_cancel _ (by positivity)]
      have hne1 : (p ^ 2) ^ (j + 1) ≠ 1 := ne_of_gt (Nat.one_lt_pow (Nat.succ_ne_zero j) (by omega))
      rw [if_pos hd, hdiv, coeff_lgF_pow_sq_pow_eq_inv_pow p hp, coeff_lgF_pow_sq_pow_eq_inv_pow p hp, if_neg hne1]
      simp [pow_succ, mul_inv, mul_comm]
  · push_neg at hn
    rw [coeff_lgF_eq_zero_of_ne_pow_sq_pow p n hn]
    have hn1 : n ≠ 1 := fun h => hn 0 (by simp [h])
    rw [if_neg hn1]
    split_ifs with hd
    · have hn' : ∀ j, n / p ^ 2 ≠ (p ^ 2) ^ j := by
        intro j hj
        apply hn (j + 1)
        rw [pow_succ, ← hj, Nat.div_mul_cancel hd]
      simp [coeff_lgF_eq_zero_of_ne_pow_sq_pow p _ hn']
    · simp
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
