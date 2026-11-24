-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.coeff_lg_lg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:35.078061+00:00
-- url     : https://prove2.me/submissions/cf42d4ef-86e8-44ac-b509-cd278b9fa6bd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_powq_modEq_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables

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
namespace CoboundarySeries
open MvPowerSeries
section Cob
variable {K : Type} [Field K]
end Cob
section Supp
variable {K : Type} [Field K]
private theorem coeff_lgF_ne_lemma_2 {p n : ℕ} (h : PowerSeries.coeff n (lgF K p) ≠ 0) :
    ∃ j, n = (p ^ 2) ^ j := by
  rw [lgF, PowerSeries.coeff_mk] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hn : n = (p ^ 2) ^ j
  · exact ⟨j, hn⟩
  · exact absurd (if_neg hn) hj
end Supp
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section MapG
variable {K : Type} [Field K]
end MapG
end CoboundarySeries
open CoboundarySeries
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {n : Fin 2 →₀ ℕ}
    (hn : n 0 ≡ p * n 1 [MOD p ^ 2 - 1]) :
    coeff n (at1 0 (lgF K p) * at1 1 (lgF K p)) = 0 := by
  rw [coeff_product_single_variables (by decide) (fun z => by fin_cases z <;> simp)]
  by_contra h
  obtain ⟨i, hi⟩ := coeff_lgF_ne_lemma_2 (left_ne_zero_of_mul h)
  obtain ⟨j, hj⟩ := coeff_lgF_ne_lemma_2 (right_ne_zero_of_mul h)
  rw [hi, hj] at hn
  have h1 : 1 ≡ p * 1 [MOD p ^ 2 - 1] :=
    ((powq_modEq_one hp i).symm.trans hn).trans ((powq_modEq_one hp j).mul_left p)
  obtain ⟨q, hq⟩ : ∃ q, q = p * p := ⟨_, rfl⟩
  have hpq : p * 2 ≤ q := hq ▸ Nat.mul_le_mul_left p hp
  have hlt1 : 1 < p ^ 2 - 1 := by rw [pow_two, ← hq]; omega
  have hltp : p < p ^ 2 - 1 := by rw [pow_two, ← hq]; omega
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, mul_one, Nat.mod_eq_of_lt hltp] at h1
  omega
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
