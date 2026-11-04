-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_public_named_jump_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:32:47.77501+00:00
-- url     : https://prove2.me/submissions/f5b1cff2-efbe-4fdf-9ad4-64347072ef83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The bounded original negative jump-test grid mean is the actual
finite significant-jump sum, with a genuine L1 limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hvanish : ∀ y : ℝ, |y| < ρ → g y = 0)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hbound : ∀ y : ℝ, ‖g y‖ₑ ≤ if y ≤ -ε then M else 0) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω : Ω, ∃ F : Finset ℝ≥0,
        (∀ t : ℝ≥0, t ∈ F ↔ 0 < t ∧ t ≤ T ∧
          ρ ≤ |X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t|) ∧
        J ω = ∑ t ∈ F,
          g (X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (𝓝 (∫ ω, J ω ∂P)) := by
  classical
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hsel (ω : Ω) :=
    avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
      X ω T hT ρ hρ g hg hvanish
  let F : Ω → Finset ℝ≥0 := fun ω => Classical.choose (hsel ω)
  let J : Ω → ℝ := fun ω => ∑ t ∈ F ω,
    g (X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)
  have hpath (ω : Ω) : Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (𝓝 (J ω)) := by
    simpa only [avram_p2_a_zero_rate_real_nnreal_uniform_step_coe] using
      (Classical.choose_spec (hsel ω)).2
  have hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (𝓝 (J ω)) :=
    Filter.Eventually.of_forall hpath
  obtain ⟨hJ, hmean⟩ :=
    avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
      P X hXm ε hε (T : ℝ) hTreal
      (fun y : ℝ => if y ≤ -ε then M else 0) M hM
      (by intro y; exact le_rfl) g hg.measurable hbound J hae
  refine ⟨J, hJ, ?_, hmean⟩
  intro ω
  exact ⟨F ω, (Classical.choose_spec (hsel ω)).1, rfl⟩
