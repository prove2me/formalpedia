-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.support_ok_log_g_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:05.653843+00:00
-- url     : https://prove2.me/submissions/2ec24dc7-61fe-472d-860b-afb4c11d4fde

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
private theorem coeff_g0F_ne_lemma {p n : ℕ} (h : PowerSeries.coeff n (g0F K p) ≠ 0) :
    ∃ j, n = p * (p ^ 2) ^ j := by
  rw [g0F, PowerSeries.coeff_mk] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hn : n = p * (p ^ 2) ^ j
  · exact ⟨j, hn⟩
  · exact absurd (if_neg hn) hj
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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) : SuppOK p (at1 0 (lgF K p) * at1 1 (g0F K p)) := by
  intro n hn
  rw [coeff_product_single_variables (by decide) (fun z => by fin_cases z <;> simp)] at hn
  obtain ⟨i, hi⟩ := coeff_lgF_ne_lemma_2 (left_ne_zero_of_mul hn)
  obtain ⟨j, hj⟩ := coeff_g0F_ne_lemma (right_ne_zero_of_mul hn)
  refine ⟨?_, ?_, ?_⟩
  · rw [hi]
    exact Nat.one_le_pow _ _ (pow_pos (by omega : 0 < p) 2)
  · rw [hj]
    exact Nat.mul_pos (by omega) (pow_pos (pow_pos (by omega) _) _)
  · rw [hi, hj]
    have h : p * (p * (p ^ 2) ^ j) = (p ^ 2) ^ (j + 1) := by ring
    rw [h]
    exact (powq_modEq_one hp i).trans (powq_modEq_one hp (j + 1)).symm
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
