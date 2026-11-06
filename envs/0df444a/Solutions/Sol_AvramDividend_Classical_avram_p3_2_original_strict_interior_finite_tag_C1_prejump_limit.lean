-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_interior_finite_tag_C1_prejump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:06:07.117836+00:00
-- url     : https://prove2.me/submissions/d86f187e-6e6a-461e-bc47-11c3dff6b0ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
    (T : Finset ℝ≥0) (z : ℕ → ℝ≥0 → ℝ)
    (u discount : ℝ≥0 → ℝ)
    (hz : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hinside : ∀ t ∈ T,
      u t ∈ U ∧
      u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ U) :
    Tendsto
      (fun k => T.sum (fun t =>
        discount t *
          (w (z k t +
            (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) -
           w (z k t)))) atTop
      (nhds (T.sum (fun t =>
        discount t *
          (w (u t +
            (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) -
           w (u t))))) := by
  have hcont : ∀ t ∈ T,
      ContinuousAt w (u t) ∧
      ContinuousAt w (u t +
        (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) := by
    intro t ht
    constructor
    · exact hw.continuousOn.continuousAt (hU.mem_nhds (hinside t ht).1)
    · exact hw.continuousOn.continuousAt (hU.mem_nhds (hinside t ht).2)
  exact avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
    X ω w T z u discount hz hcont
