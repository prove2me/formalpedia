-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitian_assembly_numeric_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:05.867712+00:00
-- url     : https://prove2.me/submissions/23b40ce8-40e9-4e14-9fdf-647f62dca270

import Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_GaussSumCharacterAverageBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_maximal_sum_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_type_cauchy_schwarz
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_maximal_sum_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_type_cauchy_schwarz
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S4 Formalism.HermitianLatticeCounting.P.S4aux Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.WeightedAmplitudeSqSumBoundTwoTypeClasses := by
  intro k r q H nn D Ty _ _ w amp μ be isBe hk hq hH hqH hnn hw hTy hbe hμ hμbe hμal hsum hamp hampbe
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5 := ⟨k - 2 * r - 5, by omega⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e1]; rw [e2] at hampbe
  have e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4) := by omega
  rw [e3] at hμbe hμal hsum
  set n : ℕ := K + (2 * r + 4) with hn
  set A0 : ℝ := H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := H ^ (4 * (r + 1)) with hA1
  have hA0p : 0 < A0 := by positivity
  have hA1p : 0 < A1 := by positivity
  by_cases hne : Nonempty Ty
  swap
  · have : IsEmpty Ty := not_nonempty_iff.1 hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    positivity
  have hqH' := hqH hne
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ 392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    obtain ⟨ε, X, hε0, hX0, hε, hX, hεb⟩ : ∃ ε X : ℝ, 0 ≤ ε ∧ 0 ≤ X ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧
        (∀ d, μ t d ≤ 2 * A0 * X) ∧ ε ^ 2 * (X * (be t ^ n)⁻¹) ≤ 49 * ((q : ℝ) ^ K)⁻¹ := by
      by_cases hb : isBe t
      · refine ⟨7 * ((q : ℝ) ^ (K + 1))⁻¹, be t ^ n, by positivity, by positivity,
          fun d => hampbe t d hb, fun d => hμbe t d hb, ?_⟩
        have h1 : be t ^ n * (be t ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        rw [h1, mul_one, mul_pow]
        have h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹ := by
          rw [inv_pow, ← pow_mul]
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        nlinarith
      · refine ⟨1, (be t / q) ^ n, zero_le_one, by positivity, fun d => by rw [one_mul]; exact hamp t d,
          fun d => hμal t d hb, ?_⟩
        have h2 : (be t / q) ^ n * (be t ^ n)⁻¹ = ((q : ℝ) ^ n)⁻¹ := by
          rw [div_pow]; field_simp
        have h3 : ((q : ℝ) ^ n)⁻¹ ≤ ((q : ℝ) ^ K)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        have h4 : 0 < ((q : ℝ) ^ K)⁻¹ := by positivity
        rw [h2]
        nlinarith
    have hms := S4aux.maximal_sum_bound D w (μ t) (amp t) ε (2 * A0 * X) hw (hμ t) hε0 hε hX
    calc _ ≤ _ := hms
      _ ≤ ε ^ 2 * (2 * A0 * X) * (4 * A1 * (be t ^ n)⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (ε ^ 2 * (X * (be t ^ n)⁻¹)) * (8 * A0 * A1 * nn) := by ring
      _ ≤ (49 * ((q : ℝ) ^ K)⁻¹) * (8 * A0 * A1 * nn) := by gcongr
      _ = _ := by ring
  have h392 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by
          gcongr
          refine le_trans ?_ hqH'
          exact_mod_cast hq
  have hexp : (r + 2) + (r + 2) + 9 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1) ≤ 39 * (r + 1) ^ 2 := by
    nlinarith
  calc _ ≤ _ := S4aux.type_cauchy_schwarz D Ty w amp hw
    _ ≤ H ^ (r + 2) * ∑ t : Ty, 392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H ^ (r + 2) * (392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H ^ (r + 2) * (H ^ (r + 2) * (H ^ 9 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        gcongr
    _ = H ^ ((r + 2) + (r + 2) + 9 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1)) * ((q : ℝ) ^ K)⁻¹ * nn := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring
    _ ≤ _ := by
        gcongr
end Formalism.HermitianLatticeCounting.P
