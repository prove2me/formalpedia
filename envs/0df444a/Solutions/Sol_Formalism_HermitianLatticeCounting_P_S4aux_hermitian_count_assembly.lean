-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hermitian_count_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:12.069048+00:00
-- url     : https://prove2.me/submissions/294fa522-466c-444d-8efc-cda4d9ee4974

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_maximal_sum_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_type_cauchy_schwarz
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
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : AssemblyNG := by
  intro c C₀
  obtain ⟨C', hC'⟩ : ∃ n : ℕ, max 1 (C₀ ^ 2) ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max 1 (C₀ ^ 2)) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  refine ⟨4 * c + C', ?_⟩
  intro k r q e H nn D Ty _ _ w amp μ be I isBe he hk hq hH hqH hnn hw hTy hbe hI hIbe hIal hμ hμM hsum hamp hampbe
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5 := ⟨k - 2 * r - 5, by omega⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e1]; rw [e2] at hampbe
  have e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4) := by omega
  rw [e3] at hμM hsum
  set B : ℝ := max 1 (C₀ ^ 2) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hHc : 0 < H ^ (c * e) := by positivity
  by_cases hne : Nonempty Ty
  swap
  · have : IsEmpty Ty := not_nonempty_iff.1 hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    positivity
  have hqH' := hqH hne
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    obtain ⟨ε, hε0, hε, hεb⟩ : ∃ ε : ℝ, 0 ≤ ε ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧
        ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹) ≤ B * ((q : ℝ) ^ K)⁻¹ := by
      by_cases hb : isBe t
      · refine ⟨|C₀| * ((q : ℝ) ^ (K + 1))⁻¹, by positivity, fun d => ?_, ?_⟩
        · refine (hampbe t d hb).trans ?_
          gcongr
          · exact hμ t d
          · exact le_abs_self _
        · have h1 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]
            exact pow_le_pow_left₀ (hI t) (hIbe t) _
          have h2 : (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ B * ((q : ℝ) ^ K)⁻¹ := by
            rw [mul_pow, sq_abs]
            have h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹ := by
              rw [inv_pow, ← pow_mul]
              apply inv_anti₀ (by positivity)
              exact pow_le_pow_right₀ hq1 (by omega)
            exact mul_le_mul (le_max_right _ _) h3 (by positivity) (by positivity)
          calc _ ≤ (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 * 1 := by gcongr
            _ ≤ _ := by rw [mul_one]; exact h2
      · refine ⟨1, zero_le_one, fun d => by rw [one_mul]; exact hamp t d, ?_⟩
        have h1 : I t ^ (K + (2 * r + 4)) ≤ be t ^ (K + (2 * r + 4)) * ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ := by
          rw [← div_eq_mul_inv, ← div_pow]
          exact pow_le_pow_left₀ (hI t) (hIal t hb) _
        have h2 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [h1]
        have h3 : ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ K)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        calc _ = I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ := by ring
          _ ≤ 1 * ((q : ℝ) ^ K)⁻¹ := by rw [one_mul]; exact h2.trans h3
          _ ≤ _ := by gcongr
    have hms := maximal_sum_bound D w (μ t) (amp t) ε (H ^ (c * e) * I t ^ (K + (2 * r + 4))) hw (hμ t) hε0 hε (hμM t)
    have hI' : 0 ≤ I t ^ (K + (2 * r + 4)) := pow_nonneg (hI t) _
    calc _ ≤ _ := hms
      _ ≤ ε ^ 2 * (H ^ (c * e) * I t ^ (K + (2 * r + 4))) * (H ^ (c * e) * (be t ^ (K + (2 * r + 4)))⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹)) * (H ^ (c * e) * H ^ (c * e) * nn) := by ring
      _ ≤ (B * ((q : ℝ) ^ K)⁻¹) * (H ^ (c * e) * H ^ (c * e) * nn) := by gcongr
      _ = _ := by ring
  have hBH : B ≤ H ^ (C' * e) := by
    calc B ≤ (2 : ℝ) ^ C' := hC'
      _ ≤ H ^ C' := by
          gcongr
          refine le_trans ?_ hqH'
          exact_mod_cast hq
      _ ≤ H ^ (C' * e) := pow_le_pow_right₀ hH (Nat.le_mul_of_pos_right _ he)
  calc _ ≤ _ := type_cauchy_schwarz D Ty w amp hw
    _ ≤ H ^ (c * e) * ∑ t : Ty, B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H ^ (c * e) * (B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H ^ (c * e) * (H ^ (c * e) * (H ^ (C' * e) * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        gcongr
    _ = _ := by
        have : H ^ ((4 * c + C') * e) = H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (C' * e) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
        rw [this]; ring
end Formalism.HermitianLatticeCounting.P.S4aux
