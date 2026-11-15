-- Prove2me | solution 1 for AvramDividend.Classical.avram_b102_original_all_spatial_stop_rows_exact_physical_jump_finsets_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:28:14.8844+00:00
-- url     : https://prove2.me/submissions/5ff81d6f-4692-4f82-bc26-b550816603e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every genuine original random clipping clock has a finite exact source-jump witness set on one conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      ∃ F : Finset ℝ≥0,
        ∀ u : ℝ≥0, u ∈ F ↔
          0 < u ∧ u ≤ κ k ω ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
  classical
  filter_upwards [
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite] with ω hω
  intro k
  let F : Finset ℝ≥0 := (hω (κ k ω)).toFinset
  refine ⟨F, ?_⟩
  intro u
  simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
