-- Prove2me | solution 1 for DeletedPrimes.counterexample_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:05:09.356219+00:00
-- url     : https://prove2.me/submissions/ff6b202a-5715-46ba-8d03-fadbebe2322e

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_window_root_aux

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α θ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hθ8 : θ < 1 / 8)
    (hθα : θ < α / 2) (hfloor : α / 2 * min (1 / 2) (1 - α) ≤ θ) :
    (2 * θ < α ∧ α ≤ 4 * θ) ∨ 1 - (1 - Real.sqrt (1 - 8 * θ)) / 2 ≤ α := by
  by_cases hα : α ≤ 1 / 2
  · left
    rw [min_eq_left (by linarith)] at hfloor
    constructor <;> linarith
  · right
    push Not at hα
    rw [min_eq_right (by linarith)] at hfloor
    have hθ0 : 0 ≤ θ := by nlinarith [mul_pos h0 (sub_pos.2 h1)]
    obtain ⟨hu1, hu2, hu3⟩ := window_root_aux hθ0 hθ8
    generalize (1 - Real.sqrt (1 - 8 * θ)) / 2 = u at hu1 hu2 hu3 ⊢
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hc) (show 0 < α + (1 - u) - 1 by linarith)]
end DeletedPrimes
