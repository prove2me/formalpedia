-- Prove2me | solution 1 for AvramDividend.Classical.ae_eq_of_common_tendstoInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T13:04:30.40663+00:00
-- url     : https://prove2.me/submissions/41a9c763-cd28-4caa-afde-0555aa462603

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Fn Gn : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hEq : ∀ n, Fn n =ᵐ[P] Gn n)
    (hFn : TendstoInMeasure P Fn atTop F)
    (hGn : TendstoInMeasure P Gn atTop G) :
    F =ᵐ[P] G := by
  have hGnOnFn : TendstoInMeasure P Fn atTop G :=
    TendstoInMeasure.congr_left (fun n => (hEq n).symm) hGn
  exact tendstoInMeasure_ae_unique hFn hGnOnFn
