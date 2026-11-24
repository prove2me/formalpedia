-- Prove2me | solution 1 for DeletedPrimes.intervalIntegrable_err_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:01:35.208803+00:00
-- url     : https://prove2.me/submissions/f35201ea-838d-4593-ac6e-81c377fe3bf0

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_abs_err_le
import Theorems.Thm_DeletedPrimes_aestronglyMeasurable_err

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => err S x ^ 2) volume a b := by
  have hb : 0 ≤ b := le_trans ha hab
  set M := (1 + |density S|) * b with hM
  have hbound : ∀ x ∈ Set.uIoc a b, ‖err S x ^ 2‖ ≤ M ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx0 : 0 ≤ x := le_trans ha (le_of_lt hx.1)
    have h1 := abs_err_le S hx0
    have h2 : (1 + |density S|) * x ≤ M := by
      rw [hM]; exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h1 h2) 2
  refine IntervalIntegrable.mono_fun' (g := fun _ => M ^ 2) intervalIntegrable_const ?_ ?_
  · exact ((aestronglyMeasurable_err S).pow 2).restrict
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall hbound
end DeletedPrimes
