-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_all_horizons_physical_negative_mark_margin_ae_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:39:51.426975+00:00
-- url     : https://prove2.me/submissions/f7157e0e-4fa2-4041-b241-17e3b78ecbbf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_b111_original_all_actual_positive_time_jump_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_a26_finite_negative_jump_support_uniform_mark_gap_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One original conull event carries a negative-mark magnitude margin on every finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -ε := by
  filter_upwards [
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite] with ω hω
  intro T
  let F : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hSupport : {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ F u ≠ 0}.Finite :=
    hω T
  have hNeg : ∀ u : ℝ≥0, 0 < u → u ≤ T → F u ≠ 0 → F u < 0 := by
    intro u hu _ hF
    exact lt_of_le_of_ne
      (avram_b111_original_all_actual_positive_time_jump_nonpositive X ω u hu)
      hF
  obtain ⟨ε, hε, hGap⟩ :=
    avram_a26_finite_negative_jump_support_uniform_mark_gap_20261114
      F T hSupport hNeg
  exact ⟨ε, hε, hGap⟩
