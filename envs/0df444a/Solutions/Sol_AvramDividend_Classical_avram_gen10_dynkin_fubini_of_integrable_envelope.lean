-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen10_dynkin_fubini_of_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:33:26.242697+00:00
-- url     : https://prove2.me/submissions/4c691f43-07f9-4b87-bd94-3172ae495c76

import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (T : ℝ) (hT : 0 ≤ T)
    (R : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry R))
    (K : Ω → ℝ) (hK : Integrable K P)
    (hb : ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ‖R ω s‖ ≤ K ω) :
    Integrable (fun ω => ∫ s in 0..T, R ω s) P ∧
    (∫ ω, (∫ s in 0..T, R ω s) ∂P) =
      ∫ s in 0..T, ∫ ω, R ω s ∂P := by
  let ν := volume.restrict (Ioc (0 : ℝ) T)
  have hb' : ∀ᵐ z ∂P.prod ν, ‖R z.1 z.2‖ ≤ K z.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with z hz hs
    exact hz z.2 ⟨hs.1.le, hs.2⟩
  have hi : Integrable (Function.uncurry R) (P.prod ν) :=
    (hK.comp_fst ν).mono' hm.aestronglyMeasurable hb'
  constructor
  · simpa only [intervalIntegral.integral_of_le hT, Function.uncurry, ν] using
      hi.integral_prod_left
  · simpa only [intervalIntegral.integral_of_le hT, Function.uncurry, ν] using
      integral_integral_swap hi
