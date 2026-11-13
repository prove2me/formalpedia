-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB185_ae_level_null_occupation_of_measurable_finite_time_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:17:37.887206+00:00
-- url     : https://prove2.me/submissions/122c57df-a551-46d0-9c02-24f12685e4c3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB184_ae_real_level_zero_singleton_mass_of_sfinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ f t = y} = 0 := by
  let μ₀ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) (n : ℝ))
  have hvol : (volume : Measure ℝ) (Ioo (0 : ℝ) (n : ℝ)) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure μ₀ := ⟨by simpa [μ₀] using hvol⟩
  let μ : Measure ℝ := μ₀.map f
  letI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map μ₀ f
  have hAtoms := avram_gbB184_ae_real_level_zero_singleton_mass_of_sfinite μ
  filter_upwards [hAtoms] with y hy
  have hMap : μ {y} =
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ f t = y} := by
    change (μ₀.map f) {y} = _
    rw [Measure.map_apply hf (measurableSet_singleton y)]
    change (volume.restrict (Ioo (0 : ℝ) (n : ℝ))) (f ⁻¹' {y}) = _
    rw [Measure.restrict_apply (hf (measurableSet_singleton y))]
    congr 1
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq]
    tauto
  exact hMap.symm.trans hy
