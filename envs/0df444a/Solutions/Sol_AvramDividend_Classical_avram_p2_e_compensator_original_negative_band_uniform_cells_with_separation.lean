-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:26:28.480411+00:00
-- url     : https://prove2.me/submissions/f6aad14f-160b-4f93-8690-3fe88e60d190

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual original negative-band jump times occupy injective uniform cells eventually. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ u ∈ F, ∀ k : ℕ, idx u k ≤ k ∧
        (idx u k : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) < u ∧
        u ≤ (((idx u k + 1 : ℕ) : ℝ≥0) *
          (T / ((k : ℝ≥0) + 1)))) ∧
      (∀ᶠ k : ℕ in atTop,
        Set.InjOn (fun u => idx u k) (F : Set ℝ≥0)) := by
  classical
  let hF := avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  let F : Finset ℝ≥0 := hF.toFinset
  have hpos : ∀ u ∈ F, 0 < u := by
    intro u hu
    exact ((Set.Finite.mem_toFinset hF).mp hu).1
  have hbound : ∀ u ∈ F, u ≤ T := by
    intro u hu
    exact ((Set.Finite.mem_toFinset hF).mp hu).2.1
  have hL : ∀ u ∈ F,
      Tendsto (fun v : ℝ≥0 => X.X v ω) (𝓝[<] u)
        (𝓝 (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
    intro u hu
    obtain ⟨l, hl⟩ := X.leftLim ω u (hpos u hu)
    haveI : (𝓝[<] u).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, hpos u hu⟩
    exact tendsto_leftLim_of_tendsto ⟨l, hl⟩
  have hR : ∀ u ∈ F,
      ContinuousWithinAt (fun v : ℝ≥0 => X.X v ω) (Ici u) u := by
    intro u hu
    exact X.rightCont ω u
  obtain ⟨idx, hidx, _⟩ :=
    avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
      (fun v : ℝ≥0 => X.X v ω) T hT F hpos hbound hL hR
  refine ⟨idx, hidx, ?_⟩
  exact avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
    T F idx (fun u hu k => (hidx u hu k).2)
