-- Prove2me | solution 1 for AvramDividend.Classical.continuous_integrable_eq_zero_of_all_set_integrals_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:53:12.152077+00:00
-- url     : https://prove2.me/submissions/5c959df8-df61-40d7-b5ef-fc87c57b66ec

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (f : ℝ → ℝ) (hc : Continuous f) (hint : Integrable f)
    (hzero : ∀ s : Set ℝ, MeasurableSet s →
      (volume : Measure ℝ) s < ∞ → (∫ x in s, f x) = 0) :
    ∀ x : ℝ, f x = 0 := by
  have hae : f =ᵐ[volume] (fun _ : ℝ => (0 : ℝ)) :=
    hint.ae_eq_zero_of_forall_setIntegral_eq_zero hzero
  have hfun : f = (fun _ : ℝ => (0 : ℝ)) :=
    (Continuous.ae_eq_iff_eq (volume : Measure ℝ)
      hc continuous_const).mp hae
  intro x
  exact congrFun hfun x
