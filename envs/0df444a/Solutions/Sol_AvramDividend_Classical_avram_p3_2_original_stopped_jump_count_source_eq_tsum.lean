-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:31:13.75834+00:00
-- url     : https://prove2.me/submissions/8c14e155-31a1-4c88-b074-f11dac98bee5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

/-- Restrict the genuine original Lévy marked jump measure to an arbitrary
measurable stopped time region; the source jump at time zero remains excluded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    [DecidablePred (fun u : ℝ≥0 => u ∈ S)]
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, (if p.1 ∈ S then F p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
            ∧ u ∈ S then
          F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        else 0 := by
  have hFstop : Measurable
      (fun p : ℝ≥0 × ℝ => if p.1 ∈ S then F p else 0) :=
    Measurable.ite (hS.preimage measurable_fst) hF measurable_const
  calc
    _ = ∑' u : ℝ≥0,
        if 0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
          (if u ∈ S then F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) else 0)
        else 0 :=
      avram_p3_2_original_source_nonlinear_jump_count_eq_tsum X ω _ hFstop
    _ = _ := by
      apply tsum_congr
      intro u
      by_cases hJump : 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      · simp [hJump]
      · simp [hJump]
