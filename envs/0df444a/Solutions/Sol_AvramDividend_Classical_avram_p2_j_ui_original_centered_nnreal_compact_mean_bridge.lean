-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:25:35.740927+00:00
-- url     : https://prove2.me/submissions/0bde478c-a6fe-48af-9ef9-341a62451208

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_named_limit_both
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_uniform_nnreal_real_mesh_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Original centered NNReal pathwise limits yield uncentered NNReal strong L1 and expected-grid limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (Z : Ω → ℝ)
    (hcenter : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω) -
           (X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω)))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
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
  have hTReal : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast hT
  have hXm : ∀ t : ℝ≥0, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hReal :=
    avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
      P X.X T g Z hcenter
  have hBoth :=
    avram_p2_j_ui_original_compact_negative_test_named_limit_both
      P X hXm g hg hc hneg (T : ℝ) hTReal Z hReal
  have hWidth (n : ℕ) :
      Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
        T / ((n : ℝ≥0) + 1) :=
    avram_p2_j_ui_uniform_nnreal_real_mesh_identification T n
  simpa only [hWidth] using hBoth
