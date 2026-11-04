-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_public_bounded_compact_grid_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:24:37.951235+00:00
-- url     : https://prove2.me/submissions/b69f85d0-4423-43b0-9298-2c37163f85ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A public original-process compact negative real-mesh mean limit
follows from actual càdlàg paths and a finite separated envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hbound : ∀ y : ℝ,
      ‖g y‖ₑ ≤ if y ≤ -ε then M else 0)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (𝓝 (∫ ω, Z ω ∂P)) := by
  classical
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hpath :=
    avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
      X T hT g hg hc hneg
  let Z : Ω → ℝ := fun ω => Classical.choose (hpath ω)
  have hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) *
              Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) *
              Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (𝓝 (Z ω)) :=
    Filter.Eventually.of_forall
      (fun ω => Classical.choose_spec (hpath ω))
  obtain ⟨hZ, hlim⟩ :=
    avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
      P X hXm ε hε (T : ℝ) hTreal
      (fun y : ℝ => if y ≤ -ε then M else 0) M hM
      (by intro y; exact le_rfl) g hg.measurable hbound Z hae
  exact ⟨Z, hZ, hlim⟩
