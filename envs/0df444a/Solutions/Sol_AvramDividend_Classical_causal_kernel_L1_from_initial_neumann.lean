-- Prove2me | solution 1 for AvramDividend.Classical.causal_kernel_L1_from_initial_neumann
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:35:24.470316+00:00
-- url     : https://prove2.me/submissions/628012a5-bf97-49c4-bb8d-21cdd295f4c6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Neumann convolution integrability at Q0=1/a implies local integrability of its kernel. -/
theorem solution
    (a : ℝ) (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (ha : 0 < a)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hI0 : ∀ x : ℝ,
      IntegrableOn (fun s : ℝ => B (x - s) * Q 0 s)
        (Ioc (0 : ℝ) x) volume) :
    ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume := by
  intro x
  have ha_inv : a * (1 / a) = (1 : ℝ) := by
    field_simp [ne_of_gt ha]
  have hmul : IntegrableOn (fun s : ℝ => a * (B (x - s) * Q 0 s))
      (Ioc (0 : ℝ) x) volume := (hI0 x).const_mul a
  apply hmul.congr_fun _ measurableSet_Ioc
  intro s hs
  calc
    a * (B (x - s) * Q 0 s) = (a * (1 / a)) * B (x - s) := by
      rw [hQ0]
      ring
    _ = B (x - s) := by rw [ha_inv]; ring
