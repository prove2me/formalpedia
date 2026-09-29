-- Prove2me | solution 1 for Diaz.conj_stable_line_generator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:53.677496+00:00
-- url     : https://prove2.me/submissions/191d4008-e261-4108-8571-44094a849f34

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {y : ℂ} (hy : ∀ q : ℚ, y ≠ (q : ℂ)) {a b : ℚ}
    (h : conj y = (a : ℂ) + (b : ℂ) * y) :
    (b = 1 ∧ a = 0 ∧ conj y = y)
      ∨ (b = -1 ∧ conj (y - (a : ℂ) / 2) = -(y - (a : ℂ) / 2)) := by
  have hcy : conj ((a : ℂ) + (b : ℂ) * y) = (a : ℂ) + (b : ℂ) * conj y := by
    simp [map_add, map_mul]
  have hinv : conj (conj y) = y := by simp
  have h2 : y = (a : ℂ) + (b : ℂ) * ((a : ℂ) + (b : ℂ) * y) :=
    calc y = conj (conj y) := hinv.symm
      _ = conj ((a : ℂ) + (b : ℂ) * y) := by rw [h]
      _ = (a : ℂ) + (b : ℂ) * conj y := hcy
      _ = (a : ℂ) + (b : ℂ) * ((a : ℂ) + (b : ℂ) * y) := by rw [h]
  have hfac : ((b : ℂ) + 1) * (((1 : ℂ) - (b : ℂ)) * y - (a : ℂ)) = 0 := by
    linear_combination h2
  have hb : b = 1 ∨ b = -1 := by
    by_contra hc
    push_neg at hc
    have hb1 : ((b : ℂ) + 1) ≠ 0 := by
      intro hz
      exact hc.2 (by exact_mod_cast (by linear_combination hz : (b : ℂ) = -1))
    have hbq : (1 : ℚ) - b ≠ 0 := fun hz => hc.1 (by linarith)
    have hlin : ((1 : ℂ) - (b : ℂ)) * y = (a : ℂ) := by
      have h3 := (mul_eq_zero.mp hfac).resolve_left hb1
      linear_combination h3
    refine hy (a / (1 - b)) ?_
    have hbqC : ((1 : ℂ) - (b : ℂ)) ≠ 0 := by
      intro hz; exact hbq (by exact_mod_cast (by linear_combination hz : ((1 : ℚ) - b : ℂ) = 0))
    push_cast
    field_simp
    linear_combination hlin
  rcases hb with rfl | rfl
  · have ha : (a : ℂ) = 0 := by linear_combination -h2 / 2
    refine Or.inl ⟨rfl, by exact_mod_cast ha, ?_⟩
    rw [h, ha]; push_cast; ring
  · refine Or.inr ⟨rfl, ?_⟩
    have hc2 : conj (2 : ℂ) = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    have hca : conj ((a : ℂ) / 2) = (a : ℂ) / 2 := by
      rw [map_div₀, hc2]; norm_num
    rw [map_sub, hca, h]
    push_cast
    ring
