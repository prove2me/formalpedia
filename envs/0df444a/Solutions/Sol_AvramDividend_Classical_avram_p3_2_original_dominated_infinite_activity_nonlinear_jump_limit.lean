-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_dominated_infinite_activity_nonlinear_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:02:14.816826+00:00
-- url     : https://prove2.me/submissions/37dad1a0-aa71-4f3a-9b43-0a66b5fb2151

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
    (w : ℝ → ℝ) (z : ℕ → ℝ≥0 → ℝ)
    (u discount : ℝ≥0 → ℝ) (bound : ℝ≥0 → ℝ)
    (hBound : Summable bound)
    (hz : ∀ t : ℝ≥0, 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
      Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hw : ∀ t : ℝ≥0, 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
      ContinuousAt w (u t) ∧
      ContinuousAt w (u t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    (hDom : ∀ᶠ k in atTop, ∀ t : ℝ≥0,
      ‖if 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
            discount t * (w ((z k) t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w ((z k) t))
          else 0‖ ≤ bound t) :
    Tendsto
      (fun k => ∑' t : ℝ≥0,
        if 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
            discount t * (w ((z k) t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w ((z k) t))
          else 0) atTop
      (nhds (∑' t : ℝ≥0,
        if 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
            discount t * (w (u t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w (u t))
          else 0)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hBound
  · intro t
    by_cases ht : 0 < t ∧
        X.X t ω - Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) t ≠ 0
    · simp only [if_pos ht]
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
      exact tendsto_const_nhds.mul (hwa.sub hwb)
    · simp only [if_neg ht]
      exact tendsto_const_nhds
  · exact hDom
