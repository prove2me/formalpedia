-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_centered_exact_path_vitali_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:33:53.073192+00:00
-- url     : https://prove2.me/submissions/191aec5a-1e78-4a5d-81b7-2e1cfb0a4105

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_existential_both

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Source-path cadlag mesh convergence supplies the eventual finite-grid limit
required by the proved original-process L1/Vitali expectation theorem. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by
  apply avram_p2_j_ui_original_centered_nnreal_compact_existential_both
    P X T hT g hg hc hneg
  filter_upwards [] with ω
  obtain ⟨F, _, hlimit⟩ :=
    avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
      X ω T hT g hg hneg
  exact ⟨_, hlimit⟩
