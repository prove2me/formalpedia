-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:11:47.352197+00:00
-- url     : https://prove2.me/submissions/bd35472e-6752-437e-ad2f-ed3f8551a482

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual post-stop negative-jump mark mass is independent of the stopped original past. -/
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
            if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧
              (X.X (τ ω + u) ω - X.X (τ ω) ω) -
              Function.leftLim (fun v : ℝ≥0 =>
                X.X (τ ω + v) ω - X.X (τ ω) ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                (X.X (τ ω + u) ω - X.X (τ ω) ω) -
                Function.leftLim (fun v : ℝ≥0 =>
                  X.X (τ ω + v) ω - X.X (τ ω) ω) u)))).toReal)
        inferInstance) P := by
  obtain ⟨W, hW, hExact⟩ := avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  have hWreal : Measurable (fun Y : ℝ≥0 → ℝ => (W Y).toReal) :=
    ENNReal.measurable_toReal.comp hW
  have hInd := avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
    X τ hτ (fun Y : ℝ≥0 → ℝ => (W Y).toReal) hWreal
  have hFun :
      (fun ω : Ω =>
        (W (fun u : ℝ≥0 => X.X (τ ω + u) ω - X.X (τ ω) ω)).toReal) =
      (fun ω : Ω =>
        (∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ (X.X (τ ω + u) ω - X.X (τ ω) ω) -
            Function.leftLim (fun v : ℝ≥0 =>
              X.X (τ ω + v) ω - X.X (τ ω) ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              (X.X (τ ω + u) ω - X.X (τ ω) ω) -
              Function.leftLim (fun v : ℝ≥0 =>
                X.X (τ ω + v) ω - X.X (τ ω) ω) u)))).toReal) := by
    funext ω
    obtain ⟨hc, hl⟩ :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag X ω (τ ω)
    exact congrArg ENNReal.toReal
      (hExact (fun u : ℝ≥0 => X.X (τ ω + u) ω - X.X (τ ω) ω) hc hl)
  rw [← hFun]
  exact hInd
