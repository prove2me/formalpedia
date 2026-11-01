-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:34:17.295762+00:00
-- url     : https://prove2.me/submissions/0424198a-dc7b-4a56-927e-f008fb9cf4b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- An increasing controlled dividend path cannot attain a fixed upper cap
at a positive deterministic time while its entire reserve prefix stays capped. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (∀ s : ℝ≥0, s ≤ T → riskProcess X x D s ω ≤ c) →
        riskProcess X x D T ω < c := by
  letI : IsProbabilityMeasure P := X.isProbability
  let e : Ω → ℝ≥0 := fun _ => T
  have hJoint : MeasurableSet
      {z : Ω × Ω | ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < 0} :=
    (avram_ws01e_b_levy_random_horizon_strict_events_measurable
      X e measurable_const 0).1
  have hEventMeas : MeasurableSet
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
        X.X T ω - X.X s ω < 0} := by
    have heq :
        {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < 0} =
        (fun ω : Ω => (ω, ω)) ⁻¹'
          {z : Ω × Ω | ∃ s : ℝ≥0, s ≤ e z.2 ∧
            X.X (e z.2) z.1 - X.X s z.1 < 0} := rfl
    rw [heq]
    exact hJoint.preimage (measurable_id.prodMk measurable_id)
  have hFull :=
    avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
      X hBV T hT
  have hNull :
      P ({ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
        X.X T ω - X.X s ω < 0}ᶜ) = 0 := by
    rw [measure_compl hEventMeas, hFull]
    all_goals simp [hFull]
  have hDraw : ∀ᵐ ω ∂P,
      ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < 0 := by
    exact hNull
  filter_upwards [hDraw] with ω hω
  intro hRange
  obtain ⟨s, hs, hlt⟩ := hω
  have hMono : Monotone (fun u : ℝ≥0 => D u ω) := hD.2.1 ω
  have hDle : D s ω ≤ D T ω := hMono hs
  have hReserve : riskProcess X x D T ω < riskProcess X x D s ω := by
    dsimp [riskProcess]
    linarith
  exact lt_of_lt_of_le hReserve (hRange s hs)
