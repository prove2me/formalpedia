-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.Tbound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:32.367178+00:00
-- url     : https://prove2.me/submissions/b0117816-4792-44cf-a74f-933acab75912

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_hD_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_hD_tele
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_rev
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_root
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_sum_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (n m : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (β : ℝ)
    (hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ β) (ζ : ℂ) (hζ1 : 1 ≤ ‖ζ‖)
    (hne : ∀ i, 1 - z i * ζ ≠ 0) :
    ‖∏ i, (1 - z i * ζ)‖ * ‖∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ)‖ ≤
      ‖ζ‖ ^ (m + 1) * (n * (‖ζ‖ ^ n * (2 ^ n * β))) := by
  set φ : ℕ → ℂ := fun a => (tp n z).coeff (n - a) with hφ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; linarith
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ (m + 1) le_rfl (by omega))
  have hDn : ∀ x, hD φ x n = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a := by
    intro x
    unfold hD
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * x ^ a) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega]
  have hrefl : ∑ b ∈ range (n + 1), φ b * ζ ^ b =
      ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * ζ ^ (n - a)) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
  have perI : ∀ i, (1 - z i * ζ) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b = ∏ l, (1 - z l * ζ) := by
    intro i
    have e1 := hD_tele φ (z i) ζ (n - 1)
    rw [show n - 1 + 1 = n by omega] at e1
    rw [e1]
    have hs := hD_succ φ (z i) (n - 1)
    rw [show n - 1 + 1 = n by omega, hDn (z i), tp_root n z i] at hs
    rw [tp_rev n z ζ hζ0, ← hrefl, sum_range_succ]
    linear_combination ζ ^ n * hs
  have perT : ∀ i, (∏ l, (1 - z l * ζ)) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
      ∑ b ∈ range n, ∑ a ∈ range (b + 1), ζ ^ (m + 1) * (ζ ^ b * (φ a * z i ^ (m + 1 + b - a))) := by
    intro i
    rw [← perI i]
    have : (1 - z i * ζ) * (∑ b ∈ range n, hD φ (z i) b * ζ ^ b) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
        (z i * ζ) ^ (m + 1) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b := by
      field_simp [hne i]
    rw [this]
    unfold hD
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl (fun b _ => sum_congr rfl (fun a ha => ?_))
    have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [show m + 1 + b - a = (m + 1) + (b - a) by omega, pow_add, mul_pow]; ring
  have key : (∏ l, (1 - z l * ζ)) * ∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ) =
      ζ ^ (m + 1) * ∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a) := by
    rw [mul_sum, sum_congr rfl (fun i _ => perT i)]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun b _ => ?_)
    rw [sum_comm]
  have hφsum : ∑ a ∈ range (n + 1), ‖φ a‖ ≤ 2 ^ n := by
    have : ∑ a ∈ range (n + 1), ‖φ a‖ = ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ := by
      rw [← Finset.sum_range_reflect (fun a => ‖(tp n z).coeff a‖) (n + 1)]
      refine sum_congr rfl (fun j hj => ?_)
      simp only [hφ]
      rw [show n + 1 - 1 - j = n - j by omega]
    rw [this]; exact tp_sum_norm n z hz
  rw [← norm_mul, key, norm_mul, norm_pow]
  gcongr
  calc ‖∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
      ≤ ∑ b ∈ range n, ‖ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ range n, ‖ζ‖ ^ n * (2 ^ n * β) := by
        refine sum_le_sum (fun b hb => ?_)
        have hbn : b < n := mem_range.mp hb
        rw [norm_mul, norm_pow]
        gcongr
        calc ‖∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
            ≤ ∑ a ∈ range (b + 1), ‖φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
          _ ≤ ∑ a ∈ range (b + 1), ‖φ a‖ * β := by
              refine sum_le_sum (fun a ha => ?_)
              have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
              rw [norm_mul]
              gcongr
              exact hβ _ (by omega) (by omega)
          _ ≤ ∑ a ∈ range (n + 1), ‖φ a‖ * β := by
              apply sum_le_sum_of_subset_of_nonneg
              · exact range_subset_range.mpr (by omega)
              · intro a _ _; positivity
          _ = (∑ a ∈ range (n + 1), ‖φ a‖) * β := by rw [sum_mul]
          _ ≤ 2 ^ n * β := by gcongr
    _ = n * (‖ζ‖ ^ n * (2 ^ n * β)) := by rw [sum_const, card_range, nsmul_eq_mul]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
