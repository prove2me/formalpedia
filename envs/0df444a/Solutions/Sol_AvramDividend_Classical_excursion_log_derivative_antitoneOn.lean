-- Prove2me | solution 1 for AvramDividend.Classical.excursion_log_derivative_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:04:13.912464+00:00
-- url     : https://prove2.me/submissions/8c22320d-eb56-4542-9c42-b8c3817c23df

import Mathlib
import Theorems.Thm_AvramDividend_Classical_excursion_real_tail_antitoneOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- An excursion-tail logarithmic derivative decreases with the height. -/
theorem solution
    (W : ℝ → ℝ) (μ : Measure ℝ) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (hW : ∀ x : ℝ, 0 < x → 0 < W x)
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    AntitoneOn (fun x : ℝ => deriv W x / W x) (Ioi (0 : ℝ)) := by
  have hratio : ∀ x : ℝ, 0 < x →
      deriv W x / W x = φ + μ.real (Ici x) := by
    intro x hx
    rw [hderiv x hx]
    have hn : W x ≠ 0 := ne_of_gt (hW x hx)
    field_simp [hn] <;> ring
  intro x hx y hy hxy
  change deriv W y / W y ≤ deriv W x / W x
  rw [hratio y hy, hratio x hx]
  have htail : μ.real (Ici y) ≤ μ.real (Ici x) :=
    (AvramDividend.Classical.excursion_real_tail_antitoneOn μ hfin) hx hy hxy
  calc
    φ + μ.real (Ici y) = μ.real (Ici y) + φ := add_comm _ _
    _ ≤ μ.real (Ici x) + φ := add_le_add_left htail φ
    _ = φ + μ.real (Ici x) := add_comm _ _
