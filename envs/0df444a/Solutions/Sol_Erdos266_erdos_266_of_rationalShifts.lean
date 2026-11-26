-- Prove2me | solution 1 for Erdos266.erdos_266_of_rationalShifts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:16.653149+00:00
-- url     : https://prove2.me/submissions/375f02ef-6448-4e46-8c7d-9f08591ea5d0

module
public import Mathlib
public import Definitions.Def_Erdos266_Glue
public import Theorems.Thm_Erdos266_not_neg_shift

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution
    (h : ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧ RationalShifts a) :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  rintro hall
  obtain ⟨a, hmono, h0, hrat⟩ := h
  have hpos : ∀ n, 1 ≤ a n := fun n => h0.trans (hmono.monotone (Nat.zero_le n))
  -- summability of the unshifted series, from the shift `t = 0`
  obtain ⟨q0, hq0⟩ := hrat 0 (not_neg_shift hpos le_rfl)
  have hsum : Summable ((1 : ℝ) / a ·) := by
    have := hq0.summable
    simpa using this
  -- the claimed irrationalizing integer shift
  obtain ⟨t, ht1, hirr⟩ := hall a ⟨hpos, hsum⟩
  -- but that shift has a rational sum
  obtain ⟨q, hq⟩ := hrat t (not_neg_shift hpos (by positivity))
  have hfun : (fun n : ℕ => (1 : ℝ) / ((a n) + ((t : ℚ) : ℝ)))
      = fun n : ℕ => (1 : ℝ) / ((a n) + (t : ℝ)) := by
    push_cast
    rfl
  have htsum : ∑' n, (1 : ℝ) / ((a n) + (t : ℝ)) = (q : ℝ) := by
    rw [← hfun]
    exact hq.tsum_eq
  exact Rat.not_irrational q (htsum ▸ hirr)
end Erdos266
