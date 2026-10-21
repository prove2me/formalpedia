-- Prove2me | solution 1 for FiniteFields.Dwork.hasSum_dworkSplittingValue
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:55:55.330281+00:00
-- url     : https://prove2.me/submissions/e67de041-253b-4cc2-91f5-2fcfc3818eb2

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
import Theorems.Thm_FiniteFields_Dwork_ramifiedTeichmullerLift_norm_of_ne_zero
section
noncomputable section
open Filter Function IsUltrametricDist Metric PowerSeries Set
open scoped NNReal Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
theorem dworkSplittingFunction_coeff (n : ℕ) :
    PowerSeries.coeff n (dworkSplittingFunction k p) =
      dworkArtinHasseParameter k p ^ n *
        PowerSeries.coeff n (dworkArtinHasseExponential k p) := by
  rw [dworkSplittingFunction, PowerSeries.coeff_rescale]
end FiniteFields.Dwork
end
end
section
noncomputable section
open scoped BigOperators WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq
@[simp]
theorem ramifiedTeichmullerLift_zero :
    ramifiedTeichmullerLift k p 0 = 0 := by
  rw [ramifiedTeichmullerLift, show teichmullerLift k p 0 = 0 by
    exact WittVector.teichmuller_zero p]
  simp
theorem ramifiedTeichmullerLift_norm (x : k) :
    ‖ramifiedTeichmullerLift k p x‖ = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, ramifiedTeichmullerLift_norm_of_ne_zero k p hx]
theorem ramifiedTeichmullerLift_norm_le_one (x : k) :
    ‖ramifiedTeichmullerLift k p x‖ ≤ 1 := by
  rw [ramifiedTeichmullerLift_norm]
  split_ifs <;> norm_num
private theorem dworkSplittingValue_argument_norm_lt_one (x : k) :
    ‖dworkArtinHasseParameter k p * ramifiedTeichmullerLift k p x‖ < 1 := by
  rw [norm_mul]
  calc
    ‖dworkArtinHasseParameter k p‖ * ‖ramifiedTeichmullerLift k p x‖ ≤
        ‖dworkArtinHasseParameter k p‖ * 1 :=
      mul_le_mul_of_nonneg_left (ramifiedTeichmullerLift_norm_le_one k p x)
        (norm_nonneg _)
    _ < 1 := by simpa using dworkArtinHasseParameter_norm_lt_one k p
section Extension
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime]
  [Field k₀] [CharP k₀ p₀] [Finite k₀]
attribute [local instance] FiniteFields.Dwork.dw4eExtensionCharP
end Extension
end FiniteFields.Dwork
end
end
open scoped BigOperators WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq
theorem solution (x : k) :
    HasSum
      (fun n : ℕ => PowerSeries.coeff n (dworkSplittingFunction k p) *
        ramifiedTeichmullerLift k p x ^ n)
      (dworkSplittingValue k p x) := by
  unfold dworkSplittingValue dworkPowerSeriesEval
  exact ((hasSum_dworkPowerSeriesEval k p (dworkArtinHasseExponential k p)
    (dworkArtinHasseParameter k p * ramifiedTeichmullerLift k p x)
    (dworkArtinHasseExponential_coeff_norm_le_one k p)
    (dworkSplittingValue_argument_norm_lt_one k p x)).summable.congr
      (fun n => by
        rw [dworkSplittingFunction_coeff, mul_pow]
        ring)).hasSum
