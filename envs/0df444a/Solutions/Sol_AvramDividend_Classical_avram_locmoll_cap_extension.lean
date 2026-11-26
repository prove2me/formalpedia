-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_cap_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:59:36.658209+00:00
-- url     : https://prove2.me/submissions/fa97d08f-9cd2-4102-a952-1602acfd97cf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_zero_extension_global_monotone_of_secant
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ V : ℝ → ℝ,
      (∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y) ∧
      (∀ y < 0, V y = 0) ∧ (∀ y, 0 ≤ V y) ∧ Monotone V ∧
      (∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u) := by 
  let V : ℝ → ℝ := fun y =>
    if C = ⊤ then w y else if y ≤ C.toReal then w y
    else w C.toReal + (y - C.toReal)
  have hVeq : ∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y := by
    intro y hy
    by_cases hc : C = ⊤
    · simp [V, hc]
    · have hle := (ENNReal.ofReal_le_iff_le_toReal hc).mp hy
      simp [V, hc, hle]
  have hVneg : ∀ y < 0, V y = 0 := by
    intro y hy
    have hle : ENNReal.ofReal y ≤ C := by
      rw [ENNReal.ofReal_eq_zero.mpr hy.le]
      exact bot_le
    rw [hVeq y hle, hw_neg y hy]
  have hV0 : 0 ≤ V 0 := by
    rw [hVeq 0 (by simp)]
    exact hw0
  have hsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u := by
    intro u v hu huv
    exact avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad
      (by intro hc y; simp [V, hc])
      (by intro hc y; simp [V, hc]) u v hu huv
  have hm := avram_wave6_08_zero_extension_global_monotone_of_secant
    V hVneg hV0 hsec
  refine ⟨V, hVeq, hVneg, ?_, hm, hsec⟩
  intro y
  by_cases hy : 0 ≤ y
  · exact hV0.trans (hm hy)
  · rw [hVneg y (lt_of_not_ge hy)]
