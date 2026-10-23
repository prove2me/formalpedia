-- Prove2me | solution 1 for AvramDividend.Classical.causal_truncated_shift_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:20:47.339869+00:00
-- url     : https://prove2.me/submissions/0177a0bf-64bf-48a9-9fee-d4ac52240ecc

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Shift a truncated causal input and remove its redundant time-window indicator. -/
theorem solution
    (g : ℝ → ℝ) (u x : ℝ) (hu : 0 ≤ u) (hux : u ≤ x) :
    (∫ t in Ioc (0 : ℝ) x,
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by
  have hx : (0 : ℝ) ≤ x := le_trans hu hux
  have hshift :
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
      (∫ s in Ioc (-u) (x - u),
        ((Ioc (0 : ℝ) x).indicator g) s ∂volume) := by
    rw [← intervalIntegral.integral_of_le hx,
      ← intervalIntegral.integral_of_le (show -u ≤ x - u by linarith)]
    simpa only [zero_sub] using
      (intervalIntegral.integral_comp_sub_right
        (f := (Ioc (0 : ℝ) x).indicator g) (d := u)
        (a := (0 : ℝ)) (b := x))
  have hset :
      Ioc (-u) (x - u) ∩ Ioc (0 : ℝ) x =
      Ioc (0 : ℝ) (x - u) := by
    ext s
    constructor
    · rintro ⟨⟨_, hsx⟩, ⟨hs0, _⟩⟩
      exact ⟨hs0, hsx⟩
    · rintro ⟨hs0, hsx⟩
      exact ⟨⟨lt_of_le_of_lt (neg_nonpos.mpr hu) hs0, hsx⟩,
        ⟨hs0, le_trans hsx (sub_le_self x hu)⟩⟩
  calc
    (∫ t in Ioc (0 : ℝ) x,
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
      (∫ s in Ioc (-u) (x - u),
        ((Ioc (0 : ℝ) x).indicator g) s ∂volume) := hshift
    _ = ∫ s in Ioc (-u) (x - u) ∩ Ioc (0 : ℝ) x, g s ∂volume :=
      MeasureTheory.setIntegral_indicator measurableSet_Ioc
    _ = ∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume := by rw [hset]
