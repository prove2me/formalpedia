-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_ae_finite_strict_large_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:01:30.755482+00:00
-- url     : https://prove2.me/submissions/b272322a-b598-4bdc-b7da-2d549dead3d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Almost surely the original BV left-jump times of size at least any
positive cutoff are finite and lie in the actual strict-after-zero
through-inclusive-horizon source interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let j : ℝ≥0 → ℝ := fun u =>
        if 0 < u ∧ u ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0
      ∀ δ : ℝ, 0 < δ →
        {u : ℝ≥0 | δ ≤ |j u|}.Finite ∧
        ∀ u : ℝ≥0, δ ≤ |j u| → 0 < u ∧ u ≤ T := by
  filter_upwards
    [avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable X hBV]
      with ω hω
  let j : ℝ≥0 → ℝ := fun u =>
    if 0 < u ∧ u ≤ T then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
    else 0
  have h0 : (0 : ℝ≥0) ≤ T := bot_le
  have hj : Summable (fun u : ℝ≥0 => |j u|) := by
    simpa only [j] using (hω 0 T h0)
  change ∀ δ : ℝ, 0 < δ →
    {u : ℝ≥0 | δ ≤ |j u|}.Finite ∧
    ∀ u : ℝ≥0, δ ≤ |j u| → 0 < u ∧ u ≤ T
  intro δ hδ
  have ht : Tendsto (fun u : ℝ≥0 => |j u|) cofinite (nhds 0) :=
    hj.tendsto_cofinite_zero
  have hlt : ∀ᶠ u : ℝ≥0 in cofinite, |j u| < δ :=
    ht.eventually (eventually_lt_nhds hδ)
  have hf : {u : ℝ≥0 | ¬ |j u| < δ}.Finite :=
    Filter.eventually_cofinite.mp hlt
  refine ⟨by simpa only [not_lt] using hf, ?_⟩
  intro u hu
  by_cases hi : 0 < u ∧ u ≤ T
  · exact hi
  · have hjz : j u = 0 := by simp [j, hi]
    have hbad : δ ≤ 0 := by simpa only [hjz, abs_zero] using hu
    exact (not_le.mpr hδ hbad).elim
