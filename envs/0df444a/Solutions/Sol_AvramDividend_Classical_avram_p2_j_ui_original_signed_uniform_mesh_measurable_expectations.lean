-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:41:29.342201+00:00
-- url     : https://prove2.me/submissions/e5d451bb-be8f-4744-80d7-7e86c6fc53e5

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_grid_measurability_from_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Measurable source coordinates discharge the exact uniform-grid measurability obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hgm : Measurable g)
    (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (Z : Ω → ℝ)
    (hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n : ℕ => ∫ ω,
          (∑ i ∈ Finset.range (n + 1),
            g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
               X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by
  apply avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
    P X ε hε T hT f M hM hf g hg Z
  · exact avram_p2_j_ui_signed_grid_measurability_from_path
      P X.X hXm g hgm (fun n : ℕ => T / ((n : ℝ) + 1))
  · exact hae
