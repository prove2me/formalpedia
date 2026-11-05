-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep9_original_BV_finite_marked_raw_jump_tail_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:51:50.767836+00:00
-- url     : https://prove2.me/submissions/4cca7d41-9cad-4b24-b89a-bcfbecff45c0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ marked : Finset ℝ≥0,
        |∑' t : {t : ℝ≥0 // t ∉ marked},
          if 0 < (t : ℝ≥0) ∧ (t : ℝ≥0) ≤ T then
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω
          else 0| < ε := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
      X hBV] with ω hω
  intro ε hε
  let f : ℝ≥0 → ℝ := fun t =>
    if 0 < t ∧ t ≤ T then
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
  have h0T : (0 : ℝ≥0) ≤ T := bot_le
  have hf : Summable f := by
    simpa only [f] using (hω 0 T h0T).1
  have htend : Tendsto
      (fun s : Finset ℝ≥0 => ∑ t ∈ s, f t)
      atTop (nhds (∑' t, f t)) := hf.hasSum
  have hevent : ∀ᶠ s : Finset ℝ≥0 in atTop,
      dist (∑ t ∈ s, f t) (∑' t, f t) < ε :=
    (Metric.tendsto_nhds.mp htend) ε hε
  obtain ⟨marked, hmarked⟩ := Filter.eventually_atTop.1 hevent
  have hdist := hmarked marked le_rfl
  have hsplit : (∑ t ∈ marked, f t) +
      (∑' t : {t : ℝ≥0 // t ∉ marked}, f t) =
      ∑' t : ℝ≥0, f t := hf.sum_add_tsum_compl
  have hEq : (∑' t : {t : ℝ≥0 // t ∉ marked}, f t) =
      (∑' t : ℝ≥0, f t) - ∑ t ∈ marked, f t := by
    linarith
  refine ⟨marked, ?_⟩
  change |∑' t : {t : ℝ≥0 // t ∉ marked}, f t| < ε
  calc
    _ = |(∑' t : ℝ≥0, f t) - ∑ t ∈ marked, f t| := congrArg abs hEq
    _ = dist (∑ t ∈ marked, f t) (∑' t, f t) := by
      simp [Real.dist_eq, abs_sub_comm]
    _ < ε := hdist
