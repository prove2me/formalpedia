-- Prove2me | solution 1 for BanditExpDesign.ec_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:34:52.33644+00:00
-- url     : https://prove2.me/submissions/5b2df1ed-0be8-4b81-bade-4cc6d728da7a

import Mathlib
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false

open BanditExpDesign in
theorem solution {K : ℕ} (hK : 2 ≤ K) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1) (t : ℕ) (ht : 1 ≤ t) :
    max ((2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α))
        (max ((2 + 2 * constC' K) ^ 2) ((2 + 2 * (K : ℝ) * (t : ℝ) ^ α) ^ 2) / (Real.exp 1 - 2) *
          Real.log (2 / δ)) ≤
      max ((2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α))
        (max ((2 + 2 * constC' K) ^ 2) ((4 + 4 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α)) /
          (Real.exp 1 - 2) * Real.log (2 / δ)) ∧
    max ((2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α))
        (max ((2 + 2 * constC' K) ^ 2) ((4 + 4 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α)) /
          (Real.exp 1 - 2) * Real.log (2 / δ)) ≤
      (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) / (Real.exp 1 - 2) *
        Real.log (2 / δ) := by
  obtain ⟨hα0, hα1⟩ := hα
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hE : 0 < Real.exp 1 - 2 := by linarith
  have hE1 : Real.exp 1 - 2 ≤ 1 := by linarith
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h2δ : Real.exp 1 < 2 / δ := by
    have h1 : δ * Real.exp 1 < 2 := (lt_div_iff₀ (Real.exp_pos 1)).1 hδ
    rw [lt_div_iff₀ hδ0]
    linarith
  have hL : 1 < Real.log (2 / δ) := (Real.lt_log_iff_exp_lt (by positivity)).2 h2δ
  have hT1 : 1 ≤ ((t : ℝ) + 1) ^ (1 + α) := Real.one_le_rpow (by linarith) (by linarith)
  have hT0 : 0 ≤ ((t : ℝ) + 1) ^ (1 + α) := by linarith
  have hu1 : 1 ≤ (t : ℝ) ^ α := Real.one_le_rpow ht' hα0
  have hu2 : (t : ℝ) ^ α * (t : ℝ) ^ α ≤ ((t : ℝ) + 1) ^ (1 + α) := by
    have a1 : (t : ℝ) ^ α ≤ ((t : ℝ) + 1) ^ α :=
      Real.rpow_le_rpow (by linarith) (by linarith) hα0
    have a2 : ((t : ℝ) + 1) ^ α * ((t : ℝ) + 1) ^ α = ((t : ℝ) + 1) ^ (α + α) :=
      (Real.rpow_add (by linarith) α α).symm
    have a3 : ((t : ℝ) + 1) ^ (α + α) ≤ ((t : ℝ) + 1) ^ (1 + α) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have a4 : (t : ℝ) ^ α * (t : ℝ) ^ α ≤ ((t : ℝ) + 1) ^ α * ((t : ℝ) + 1) ^ α :=
      mul_le_mul a1 a1 (by linarith) (by linarith)
    linarith
  have hC0 : 0 ≤ constC' K := by unfold constC'; positivity
  have hKC : 4 + 4 * (K : ℝ) ≤ 2 + 2 * constC' K := by
    unfold constC'
    have hee : 1 ≤ Real.exp 1 ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hee (sq_nonneg (K : ℝ))]
  have hY : (4 + 4 * (K : ℝ)) ^ 2 ≤ (2 + 2 * constC' K) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hKC 2
  have hX : (2 + 2 * (K : ℝ) * (t : ℝ) ^ α) ^ 2 ≤
      (4 + 4 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) := by
    have b1 : 2 + 2 * (K : ℝ) * (t : ℝ) ^ α ≤ (2 + 2 * (K : ℝ)) * (t : ℝ) ^ α := by nlinarith
    have b2 : (2 + 2 * (K : ℝ) * (t : ℝ) ^ α) ^ 2 ≤ ((2 + 2 * (K : ℝ)) * (t : ℝ) ^ α) ^ 2 :=
      pow_le_pow_left₀ (by positivity) b1 2
    have b3 : ((2 + 2 * (K : ℝ)) * (t : ℝ) ^ α) ^ 2 =
        (2 + 2 * (K : ℝ)) ^ 2 * ((t : ℝ) ^ α * (t : ℝ) ^ α) := by ring
    have b4 : (2 + 2 * (K : ℝ)) ^ 2 * ((t : ℝ) ^ α * (t : ℝ) ^ α) ≤
        (2 + 2 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) :=
      mul_le_mul_of_nonneg_left hu2 (by positivity)
    have b5 : (2 + 2 * (K : ℝ)) ^ 2 ≤ (4 + 4 * (K : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have b6 : (2 + 2 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) ≤
        (4 + 4 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) :=
      mul_le_mul_of_nonneg_right b5 hT0
    linarith
  refine ⟨?_, ?_⟩
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (max_le_max le_rfl hX) hE.le) (by linarith))
  · have hW0 : 0 ≤ (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) := by positivity
    have hWZ : (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) ≤
        (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) / (Real.exp 1 - 2) *
          Real.log (2 / δ) := by
      have c1 := le_div_self hW0 hE hE1
      have c2 : (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) / (Real.exp 1 - 2) ≤
          (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) / (Real.exp 1 - 2) *
            Real.log (2 / δ) :=
        le_mul_of_one_le_right (div_nonneg hW0 hE.le) hL.le
      linarith
    apply max_le
    · have d1 : 2 * constC' K + 1 ≤ (2 + 2 * constC' K) ^ 2 := by nlinarith
      have d2 := mul_le_mul_of_nonneg_right d1 hT0
      linarith
    · refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      refine div_le_div_of_nonneg_right ?_ hE.le
      apply max_le
      · exact le_mul_of_one_le_right (sq_nonneg _) hT1
      · exact mul_le_mul_of_nonneg_right hY hT0
