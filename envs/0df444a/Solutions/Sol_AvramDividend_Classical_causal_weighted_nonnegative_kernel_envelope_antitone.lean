-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_nonnegative_kernel_envelope_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:43:36.101018+00:00
-- url     : https://prove2.me/submissions/1e529ba7-be16-4802-bc91-4767eb438499

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- An exponentially damped nonnegative causal envelope remains antitone. -/
theorem solution
    (K : ℝ → ℝ) (w β : ℝ) (hw : 0 ≤ w)
    (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hK0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ K t) :
    AntitoneOn (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hearg : -w * y ≤ -w * x := by
    have h := mul_le_mul_of_nonneg_left hxy hw
    nlinarith
  have he : Real.exp (-w * y) ≤ Real.exp (-w * x) :=
    Real.exp_le_exp.mpr hearg
  have hsum : |β| + K y ≤ |β| + K x := by
    simpa only [add_comm] using
      (add_le_add_left (hanti hx hy hxy) (|β|))
  calc
    Real.exp (-w * y) * (|β| + K y)
        ≤ Real.exp (-w * x) * (|β| + K y) :=
          mul_le_mul_of_nonneg_right he (add_nonneg (abs_nonneg β) (hK0 y hy))
    _ ≤ Real.exp (-w * x) * (|β| + K x) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
