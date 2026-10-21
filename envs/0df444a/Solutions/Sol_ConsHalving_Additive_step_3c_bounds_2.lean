-- Prove2me | solution 2 for ConsHalving.Additive.step_3c_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:23:21.817006+00:00
-- url     : https://prove2.me/submissions/e6fbb44a-d2e2-45f0-aa35-837179323851

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem ch_gamma_nonneg {m : ℕ} (x y : Fin m → ℝ) (hx : IsFractional x) (j : Fin m)
    (hne : y j ≠ x j) : 0 ≤ gamma x y j := by
  unfold gamma
  split_ifs with h
  · exact div_nonneg (by linarith [(hx j).2]) (by linarith)
  · have : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    exact div_nonneg (hx j).1 (by linarith)

theorem ch_step_mem {m : ℕ} (x y : Fin m → ℝ) (hx : IsFractional x) (j : Fin m)
    (hne : y j ≠ x j) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ gamma x y j) :
    0 ≤ stepPoint x y γ j ∧ stepPoint x y γ j ≤ 1 := by
  unfold gamma at h1
  unfold stepPoint
  have hxj := hx j
  split_ifs at h1 with h
  · have hpos : 0 < y j - x j := by linarith
    have := (le_div_iff₀ hpos).mp h1
    constructor <;> nlinarith [hxj.1, hxj.2, mul_nonneg h0 hpos.le]
  · have hlt : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    have hpos : 0 < x j - y j := by linarith
    have := (le_div_iff₀ hpos).mp h1
    constructor <;> nlinarith [hxj.1, hxj.2, mul_nonneg h0 hpos.le]

theorem ch_step_jstar {m : ℕ} (x y : Fin m → ℝ) (j : Fin m) (hne : y j ≠ x j) :
    stepPoint x y (gamma x y j) j = 0 ∨ stepPoint x y (gamma x y j) j = 1 := by
  unfold stepPoint gamma
  split_ifs with h
  · right
    have hd : y j - x j ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  · left
    have hlt : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    have hd : x j - y j ≠ 0 := by linarith
    field_simp
    ring

theorem solution {m : ℕ} (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsFractional x) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsFractional (stepPoint x y (gamma x y jstar)) ∧
      (∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j) ∧
      (stepPoint x y (gamma x y jstar) jstar = 0 ∨
        stepPoint x y (gamma x y jstar) jstar = 1) := by
  have h0 : 0 ≤ gamma x y jstar := ch_gamma_nonneg x y hx jstar hstar
  have key : ∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j := by
    intro j hj
    simp only [stepPoint, hj]
    ring
  refine ⟨fun j => ?_, key, ch_step_jstar x y jstar hstar⟩
  by_cases hne : y j = x j
  · rw [key j hne]
    exact hx j
  · exact ch_step_mem x y hx j hne _ h0 (hmin j hne)
