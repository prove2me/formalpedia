-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:03:45.225971+00:00
-- url     : https://prove2.me/submissions/45ef5541-6836-40c7-a42b-759deebe4f8b

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_diverges_of_levy_activity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- BV standing Lévy conditions already supply the quadratic moment needed for the canonical infinite-origin kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hνinf : X.ν (Iio (0 : ℝ)) = ⊤ := by
    by_contra hne
    exact hInfinite (lt_top_iff_ne_top.mpr hne)
  exact bv_esscher_positive_tail_kernel_diverges_of_levy_activity
    X hX hbv q hq φ hφ hroot X.ν_integrable hνinf
