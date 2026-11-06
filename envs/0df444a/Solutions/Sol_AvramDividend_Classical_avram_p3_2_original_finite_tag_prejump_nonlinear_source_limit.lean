-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:02:07.712662+00:00
-- url     : https://prove2.me/submissions/b91b8bcc-8d3a-4af9-8c76-32cf7cac4d2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (w : ℝ → ℝ) (T : Finset ℝ≥0)
    (z : ℕ → ℝ≥0 → ℝ) (u discount : ℝ≥0 → ℝ)
    (hz : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hw : ∀ t ∈ T,
      ContinuousAt w (u t) ∧
      ContinuousAt w (u t +
        (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t))) :
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
  apply tendsto_finset_sum T
  intro t ht
  let d : ℝ := X.X t ω -
    Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
  have hplus : Tendsto (fun k => z k t + d) atTop
      (nhds (u t + d)) := (hz t ht).add tendsto_const_nhds
  have hwa : Tendsto (fun k => w (z k t + d)) atTop
      (nhds (w (u t + d))) :=
    (hw t ht).2.tendsto.comp hplus
  have hwb : Tendsto (fun k => w (z k t)) atTop
      (nhds (w (u t))) :=
    (hw t ht).1.tendsto.comp (hz t ht)
  change Tendsto
    (fun k => discount t * (w (z k t + d) - w (z k t)))
    atTop (nhds (discount t * (w (u t + d) - w (u t))))
  exact tendsto_const_nhds.mul (hwa.sub hwb)
