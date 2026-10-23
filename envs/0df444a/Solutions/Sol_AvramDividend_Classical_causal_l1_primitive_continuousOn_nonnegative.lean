-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_primitive_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:12:33.870872+00:00
-- url     : https://prove2.me/submissions/cfec2bdc-124d-4ba2-9d22-c54a985cb09b

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

theorem solution
    (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, K s ∂volume)
      (Ici (0 : ℝ)) := by
  let f : ℝ → ℝ := (Ioi (0 : ℝ)).indicator K
  have hIntegrable : Integrable f volume :=
    hK.integrable_indicator measurableSet_Ioi
  have hInterval : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    exact hIntegrable.intervalIntegrable
  have hContinuous : Continuous (fun x : ℝ =>
      ∫ s in (0 : ℝ)..x, f s ∂volume) :=
    intervalIntegral.continuous_primitive hInterval 0
  have hEq (x : ℝ) (hx : 0 ≤ x) :
      (∫ s in Ioc (0 : ℝ) x, K s ∂volume) =
      (∫ s in (0 : ℝ)..x, f s ∂volume) := by
    rw [intervalIntegral.integral_of_le hx]
    change (∫ s in Ioc (0 : ℝ) x, K s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x,
        (Ioi (0 : ℝ)).indicator K s ∂volume)
    rw [setIntegral_indicator measurableSet_Ioi]
    have hsubset : Ioc (0 : ℝ) x ⊆ Ioi (0 : ℝ) := by
      intro s hs
      exact hs.1
    rw [inter_eq_left.mpr hsubset]
  apply hContinuous.continuousOn.congr
  intro x hx
  exact hEq x hx
