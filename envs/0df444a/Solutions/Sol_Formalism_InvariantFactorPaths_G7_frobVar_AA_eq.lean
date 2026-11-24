-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.frobVar_AA_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:48.157509+00:00
-- url     : https://prove2.me/submissions/1d44af64-3f80-47a9-9cf4-10444eed2651

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ppowq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_finset_fin_two_eq_cases
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_AA_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_AA_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {x y : Fin 2}
    (hxy : x ≠ y) :
    frobVar p (AA K p x y) =
      MvPowerSeries.C (p : K) * (at1 x (g0F K p) * at1 y (lgF K p) - AA K p y x) := by
  ext n
  rw [MvPowerSeries.coeff_C_mul, map_sub, coeff_product_single_variables hxy (finset_fin_two_eq_cases x y hxy)]
  by_cases hc : ∃ a b, n x = p * (p ^ 2) ^ a ∧ n y = (p ^ 2) ^ b
  · obtain ⟨a, b, hnx, hny⟩ := hc
    rw [hnx, hny, coeff_g0F_of K hp, coeff_lgF_pow K hp]
    by_cases hab : b ≤ a
    · rw [coeff_AA_of K hp hab hny hnx]
      have h0 : MvPowerSeries.coeff n (frobVar p (AA K p x y)) = 0 := by
        by_contra hne
        obtain ⟨i, j, hij, hx, hy⟩ := coeff_frobVar_AA_ne_zero hp hne
        have e1 := ppowq_inj hp (hnx.symm.trans hx)
        have e2 := powq_inj hp (hny.symm.trans hy)
        omega
      have e : ((p : K) ^ (a + 1))⁻¹ * ((p : K) ^ b)⁻¹ = ((p : K) ^ (b + a + 1))⁻¹ := by
        rw [← mul_inv, ← pow_add]
        congr 2
        omega
      rw [h0, e, sub_self, mul_zero]
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [coeff_frobVar_AA_of K hp hxy (show a ≤ b' by omega) hnx hny]
      have h0 : MvPowerSeries.coeff n (AA K p y x) = 0 := by
        by_contra hne
        obtain ⟨i, j, hij, hy, hx⟩ := coeff_AA_ne_zero hne
        have e1 := ppowq_inj hp (hnx.symm.trans hx)
        have e2 := powq_inj hp (hny.symm.trans hy)
        omega
      rw [h0, sub_zero]
      field_simp
      ring
  · have h1 : MvPowerSeries.coeff n (frobVar p (AA K p x y)) = 0 := by
      by_contra hne
      obtain ⟨i, j, _, hx, hy⟩ := coeff_frobVar_AA_ne_zero hp hne
      exact hc ⟨i, j + 1, hx, hy⟩
    have h2 : MvPowerSeries.coeff n (AA K p y x) = 0 := by
      by_contra hne
      obtain ⟨i, j, _, hy, hx⟩ := coeff_AA_ne_zero hne
      exact hc ⟨j, i, hx, hy⟩
    have h3 : PowerSeries.coeff (n x) (g0F K p) * PowerSeries.coeff (n y) (lgF K p) = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := coeff_g0F_ne_zero (left_ne_zero_of_mul hne)
      obtain ⟨b, hb⟩ := coeff_lgF_ne_zero (right_ne_zero_of_mul hne)
      exact hc ⟨a, b, ha, hb⟩
    rw [h1, h2, h3, sub_zero, mul_zero]
end Formalism.InvariantFactorPaths.G7
