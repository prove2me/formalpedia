-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:18:00.513333+00:00
-- url     : https://prove2.me/submissions/665d7e28-b4c6-4380-8788-7bb09c84360d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Identify the integrable original-source limit with the genuine finite jump-test sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g ((X.X u ω - X.X 0 ω) -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F, g ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)) ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - J)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, J ω ∂P)) := by
  classical
  have hPath (ω : Ω) :=
    avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
      X ω T hT g hg hneg
  let F : Ω → Finset ℝ≥0 := fun ω => Classical.choose (hPath ω)
  let J : Ω → ℝ := fun ω =>
    ∑ u ∈ F ω, g ((X.X u ω - X.X 0 ω) -
      Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)
  have hSpec (ω : Ω) := Classical.choose_spec (hPath ω)
  have hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω) -
           (X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω)))
      atTop (nhds (J ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [J, F] using (hSpec ω).2
  obtain ⟨hJ, hL1, hMean⟩ :=
    avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge
      P X T hT g hg hc hneg J hae
  have hRep (ω : Ω) : ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        g ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
      J ω = ∑ u ∈ F, g ((X.X u ω - X.X 0 ω) -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) := by
    refine ⟨F ω, ?_, rfl⟩
    exact (hSpec ω).1
  exact ⟨J, hJ, hRep, hL1, hMean⟩
