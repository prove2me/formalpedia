-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_input_primitive_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:12:20.240034+00:00
-- url     : https://prove2.me/submissions/7a3ae744-c715-4c4a-9f6c-a4e9f25fb6b9

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

theorem solution
    (V : ℝ → ℝ)
    (hV : ContinuousOn V (Ici (0 : ℝ))) :
    ContinuousOn (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, V s ∂volume)
      (Ici (0 : ℝ)) := by
  let F : ℝ → ℝ := fun x => V (max x 0)
  have hmax : Continuous (fun x : ℝ => max x 0) :=
    continuous_id.max continuous_const
  have hF : Continuous F := by
    exact hV.comp_continuous hmax (by
      intro x
      change (0 : ℝ) ≤ max x 0
      exact le_max_right x 0)
  have hI : ∀ a b : ℝ, IntervalIntegrable F volume a b := by
    intro a b
    exact hF.intervalIntegrable a b
  have hPrim : Continuous (fun x : ℝ =>
      ∫ s in (0 : ℝ)..x, F s ∂volume) :=
    intervalIntegral.continuous_primitive hI 0
  have hEq : ∀ x ∈ Ici (0 : ℝ),
      (∫ s in Ioc (0 : ℝ) x, V s ∂volume) =
      (∫ s in (0 : ℝ)..x, F s ∂volume) := by
    intro x hx
    change (0 : ℝ) ≤ x at hx
    rw [intervalIntegral.integral_of_le hx]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1.le
    simp only [F, max_eq_left hs0]
  exact hPrim.continuousOn.congr hEq
