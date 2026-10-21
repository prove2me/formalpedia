-- Prove2me | solution 1 for ConsHalving.Additive.step_3c_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:21.905779+00:00
-- url     : https://prove2.me/submissions/7dca70bc-0a50-4c6c-9fa4-68301ab2053b

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

open ConsHalving.Additive

private lemma gamma_nonneg_aux (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : b ≠ a) :
    0 ≤ (if a < b then (1 - a) / (b - a) else a / (a - b)) := by
  split_ifs with h
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg ha0 (by push_neg at h; linarith)

private lemma coord_bounds (a b t : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : b ≠ a) (ht0 : 0 ≤ t)
    (ht : t ≤ (if a < b then (1 - a) / (b - a) else a / (a - b))) :
    0 ≤ (1 - t) * a + t * b ∧ (1 - t) * a + t * b ≤ 1 := by
  have e : (1 - t) * a + t * b = a + t * (b - a) := by ring
  rw [e]
  split_ifs at ht with h
  · have hp : 0 < b - a := by linarith
    rw [le_div_iff₀ hp] at ht
    constructor <;> nlinarith
  · have hp : 0 < a - b := by
      push_neg at h
      exact lt_of_le_of_ne (by linarith) (fun h' => hab (by linarith))
    rw [le_div_iff₀ hp] at ht
    constructor <;> nlinarith

private lemma coord_end (a b : ℝ) (hab : b ≠ a) :
    let t := (if a < b then (1 - a) / (b - a) else a / (a - b))
    (1 - t) * a + t * b = 0 ∨ (1 - t) * a + t * b = 1 := by
  intro t
  have e : (1 - t) * a + t * b = a + t * (b - a) := by ring
  rw [e]
  by_cases h : a < b
  · right
    have hp : b - a ≠ 0 := by linarith
    simp only [t, if_pos h]
    rw [div_mul_cancel₀ _ hp]
    ring
  · left
    have hp : a - b ≠ 0 := fun h' => hab (by linarith)
    simp only [t, if_neg h]
    have : a / (a - b) * (b - a) = -(a / (a - b) * (a - b)) := by ring
    rw [this, div_mul_cancel₀ _ hp]
    ring

theorem solution {m : ℕ} (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsFractional x) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsFractional (stepPoint x y (gamma x y jstar)) ∧
      (∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j) ∧
      (stepPoint x y (gamma x y jstar) jstar = 0 ∨ stepPoint x y (gamma x y jstar) jstar = 1) := by
  have g0 : 0 ≤ gamma x y jstar :=
    gamma_nonneg_aux (x jstar) (y jstar) (hx jstar).1 (hx jstar).2 hstar
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases hj : y j = x j
    · unfold stepPoint
      rw [hj]
      refine ⟨by nlinarith [(hx j).1], by nlinarith [(hx j).2]⟩
    · exact coord_bounds (x j) (y j) _ (hx j).1 (hx j).2 hj g0 (hmin j hj)
  · unfold stepPoint
    rw [hj]
    ring
  · exact coord_end (x jstar) (y jstar) hstar
