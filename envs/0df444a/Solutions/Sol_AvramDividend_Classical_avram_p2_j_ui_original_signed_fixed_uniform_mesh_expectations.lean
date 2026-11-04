-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:28:24.576252+00:00
-- url     : https://prove2.me/submissions/e91d9203-e462-4b1e-8f43-84862e798a35

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_plus_one_grid_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_positive_plus_one_mesh_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Exact uniform positive mesh, genuine source signed increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (Z : Ω → ℝ)
    (hm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) P)
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
  obtain ⟨hmesh, hhor⟩ := avram_p2_j_ui_positive_plus_one_mesh_horizon T hT
  apply avram_p2_j_ui_original_signed_plus_one_grid_expectations
    P X ε hε T (le_of_lt hT) f M hM hf g hg
    (fun n : ℕ => T / ((n : ℝ) + 1))
    (fun n ω => ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
         X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω))
    Z
  · intro n ω
    rfl
  · exact hmesh
  · exact Eventually.of_forall (fun n => le_of_eq (hhor n))
  · exact hm
  · exact hae
