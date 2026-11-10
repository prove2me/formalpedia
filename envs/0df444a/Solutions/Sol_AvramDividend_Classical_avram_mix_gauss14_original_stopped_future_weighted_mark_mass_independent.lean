-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:21:08.822799+00:00
-- url     : https://prove2.me/submissions/a03a73ed-e491-40f8-af7f-2ada8813d110

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Weighted jumps over a future stopping-time window are independent of the true stopped past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω =>
          (∫⁻ p : ℝ≥0 × ℝ,
            if τ ω < p.1 ∧ p.1 ≤ τ ω + T then g p.2 else 0 ∂
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧ X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)
        inferInstance) P := by
  have hInd :=
    avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
      X τ hτ T g hg
  have hEq :
      (fun ω : Ω =>
        (∫⁻ p : ℝ≥0 × ℝ,
          if τ ω < p.1 ∧ p.1 ≤ τ ω + T then g p.2 else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal) =
      (fun ω : Ω =>
        (∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧
              (X.X (τ ω + u) ω - X.X (τ ω) ω) -
              Function.leftLim (fun v : ℝ≥0 =>
                X.X (τ ω + v) ω - X.X (τ ω) ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              (X.X (τ ω + u) ω - X.X (τ ω) ω) -
              Function.leftLim (fun v : ℝ≥0 =>
                X.X (τ ω + v) ω - X.X (τ ω) ω) u)))).toReal) := by
    funext ω
    exact (congrArg ENNReal.toReal
      (avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
        X ω (τ ω) T g hg)).symm
  rw [hEq]
  exact hInd
