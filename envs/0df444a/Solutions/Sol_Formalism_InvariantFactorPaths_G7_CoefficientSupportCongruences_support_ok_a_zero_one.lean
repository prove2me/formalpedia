-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.support_ok_a_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:57.023868+00:00
-- url     : https://prove2.me/submissions/8d348396-44fe-4be4-aaac-ad7879189325

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_FG_InjVAux_Good_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
import Theorems.Thm_Formalism_LT_InvIntP_key
import Theorems.Thm_Formalism_LT_LTL_Cong_pow
import Theorems.Thm_Formalism_LT_LTL_Near_pow

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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
namespace CoefficientSupportCongruences
open FrobeniusSubstitution
section Supp
variable {K : Type} [Field K]
private theorem exists_pow_of_coeff_AA_ne_zero {p : ℕ} {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    (h : MvPowerSeries.coeff n (AA K p x y) ≠ 0) :
    ∃ i j : ℕ, n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j := by
  have h' : AA K p x y n ≠ 0 := h
  simp only [AA] at h'
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  split_ifs at hj with hc
  · exact ⟨i, j, hc.2.1, hc.2.2⟩
  · exact absurd rfl hj
private theorem pow_sq_pow_modEq_one_sq_sub_one {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    (p ^ 2) ^ i ≡ 1 [MOD p ^ 2 - 1] := by
  have key : p ^ 2 ≡ 1 [MOD p ^ 2 - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))
  simpa using key.pow i
end Supp
end CoefficientSupportCongruences
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) : SuppOK p (AA K p 0 1) := by
  intro n hn
  obtain ⟨i, j, hi, hj⟩ := exists_pow_of_coeff_AA_ne_zero hn
  have hp0 : 0 < p := by omega
  rw [hi, hj]
  refine ⟨pow_pos (pow_pos hp0 2) i, Nat.mul_pos hp0 (pow_pos (pow_pos hp0 2) j), ?_⟩
  have h2 : p * (p * (p ^ 2) ^ j) = (p ^ 2) ^ (j + 1) := by ring
  rw [h2]
  exact (pow_sq_pow_modEq_one_sq_sub_one hp i).trans (pow_sq_pow_modEq_one_sq_sub_one hp (j + 1)).symm
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
