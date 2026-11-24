-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.localZeroSumBoundOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:21.851851+00:00
-- url     : https://prove2.me/submissions/dbc675a6-08dc-4e09-be71-23ecb7b70b57

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZerosOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_sub_le_re_of_mem_closedBall
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_center_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_sum_div_sub
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_le_div_log_two_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : LocalZerosOf := by
  intro hLan hGr hInv
  obtain ⟨C, hC⟩ := hGr
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hCC : C ≤ C₁ := le_max_left _ _
  refine ⟨120 * (1 + Real.log (22 * C₁) / Real.log 2), ?_⟩
  intro q _ χ hχ t
  set z₀ : ℂ := (11 / 10 : ℂ) + t * I with hz₀
  have hz₀re : z₀.re = 11 / 10 := by
    rw [hz₀, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    norm_num
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set M : ℝ := 22 * C₁ * q * (|t| + 2) with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ C₁ * q := by nlinarith
    nlinarith
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (3 / 5)) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hnz : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := fun s hs =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 := hnz z₀ (by rw [hz₀re]; norm_num)
  have hlow : 1 / 11 ≤ ‖DirichletCharacter.LFunction χ z₀‖ := by
    have h := hInv q χ z₀ (by rw [hz₀re]; norm_num)
    rw [hz₀re, show (11 / 10 : ℝ) / (11 / 10 - 1) = 11 by norm_num] at h
    have hpos : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    rw [inv_le_comm₀ hpos (by norm_num)] at h
    calc (1 / 11 : ℝ) = (11 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := h
  have hbound : ∀ z ∈ Metric.closedBall z₀ (3 / 5),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre : 1 / 2 ≤ z.re := by
      have := re_sub_le_re_of_mem_closedBall hz
      rw [hz₀re] at this
      linarith
    have h1 := hC q χ hχ z hre
    have hn : ‖z‖ ≤ 11 / 10 + |t| + 3 / 5 := by
      have := norm_le_norm_add_of_mem_closedBall hz
      have := norm_center_le t
      linarith
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ C₁ * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hq0) (by linarith)
      _ ≤ C₁ * q * (2 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hq0)
      _ = M * (1 / 11) := by rw [hM]; ring
      _ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
  obtain ⟨Z, m, hZ, hm1, hm2, -, happrox⟩ :=
    hLan (DirichletCharacter.LFunction χ) z₀ (3 / 5) M (by norm_num) hM1 hdiff hf0 hbound
  refine ⟨Z, m, ?_, hm1, hm2, ?_⟩
  · intro ρ
    rw [hZ ρ, show (3 / 5 : ℝ) / 3 = 1 / 5 by norm_num]
  · intro σ hσ1 hσ2
    set s : ℂ := (σ : ℂ) + t * I with hs
    have hsre : s.re = σ := by
      rw [hs, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    have hsball : s ∈ Metric.closedBall z₀ ((3 / 5) / 6) := by
      rw [Metric.mem_closedBall, dist_eq_norm, show (3 / 5 : ℝ) / 6 = 1 / 10 by norm_num]
      have hd : s - z₀ = ((σ - 11 / 10 : ℝ) : ℂ) := by
        rw [hs, hz₀]
        push_cast
        ring
      rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hnz s (by rw [hsre]; exact hσ1)
    have hA := happrox s hsball hfs
    have hpos1 : 0 < 22 * C₁ := by linarith
    have hpos2 : 0 < (q : ℝ) * (|t| + 2) := by positivity
    have hL : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hlogM : Real.log M ≤
        (1 + Real.log (22 * C₁) / Real.log 2) * Real.log ((q : ℝ) * (|t| + 2)) := by
      have hMe : M = (22 * C₁) * ((q : ℝ) * (|t| + 2)) := by rw [hM]; ring
      rw [hMe, Real.log_mul hpos1.ne' hpos2.ne']
      have := log_le_div_log_two_mul C₁ _ hC₁ hL
      nlinarith
    have hre := Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    have hre' := neg_abs_le
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
    rw [Complex.sub_re, re_sum_div_sub] at hre hre'
    have h72 : 72 * Real.log M / (3 / 5) = 120 * Real.log M := by ring
    rw [h72] at hA
    have hneg : (negLD χ s).re =
        -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s).re := by
      rw [negLD, Complex.neg_re]
    rw [hneg]
    nlinarith
end Formalism.ZeroFreeDirichlet
