-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_compact_negative_test_named_limit_both
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:37:55.76078+00:00
-- url     : https://prove2.me/submissions/1659d10c-bb42-476a-9c18-1e9a7e53237e

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_test_finite_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_grid_measurability_from_path
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_strong_L1
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Named original jump-sum limits inherit strong L1 and genuine expectation convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (T : ℝ) (hT : 0 < T)
    (Z : Ω → ℝ)
    (hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by
  obtain ⟨ε, hε, M, hM, hbound⟩ :=
    avram_p2_j_ui_compact_negative_test_finite_envelope g hg hc hneg
  have hm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) P := by
    exact avram_p2_j_ui_signed_grid_measurability_from_path
      P X.X hXm g hg.measurable
        (fun n : ℕ => T / ((n : ℝ) + 1))
  have hStrong :=
    avram_p2_j_ui_original_signed_uniform_mesh_strong_L1
      P X ε hε T hT (fun y => ‖g y‖ₑ) M hM hbound
      g (fun y => le_rfl) Z hm hae
  have hMean :=
    avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
      P X hXm ε hε T hT (fun y => ‖g y‖ₑ) M hM hbound
      g hg.measurable (fun y => le_rfl) Z hae
  exact ⟨hMean.1, hStrong.2, hMean.2⟩
