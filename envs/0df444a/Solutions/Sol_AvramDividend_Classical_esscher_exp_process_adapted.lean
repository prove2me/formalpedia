-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_process_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:01:22.142253+00:00
-- url     : https://prove2.me/submissions/4030f1a7-2607-47e9-a843-6a492a7e0bd7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) :
    Adapted 𝓕 (fun (t : ℝ≥0) (ω : Ω) =>
      Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by
  intro t
  change Measurable[𝓕 t]
    (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))
  exact Real.measurable_exp.comp ((((X.adapted t).const_mul θ).sub measurable_const))
