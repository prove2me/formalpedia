-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_physical_clock_zero_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:07:49.096046+00:00
-- url     : https://prove2.me/submissions/79d27381-0c69-402e-98ca-50b243b5e12f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical stopped time law has no atom at zero; exact zero-drift integral, variant 4. -/
theorem solution
    (T : ℝ) (F : ℝ≥0 → ℝ) (hF : ∀ t, t ≠ 0 → F t = 0) :
    (∫ t, F t ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) = 0 := by
  let μ : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
  have hZero : μ ({0} : Set ℝ≥0) = 0 := by
    change (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) {0} = 0
    rw [Measure.map_apply measurable_real_toNNReal (measurableSet_singleton (0 : ℝ≥0))]
    rw [Measure.restrict_apply (measurable_real_toNNReal (measurableSet_singleton (0 : ℝ≥0)))]
    have hSubset :
        (Real.toNNReal ⁻¹' ({0} : Set ℝ≥0)) ∩ Icc (0 : ℝ) T ⊆
          ({0} : Set ℝ) := by
      intro t ht
      have hz : Real.toNNReal t = 0 := ht.1
      have ht0 : t ≤ 0 := Real.toNNReal_eq_zero.mp hz
      exact Set.mem_singleton_iff.mpr (le_antisymm ht0 ht.2.1)
    exact le_antisymm
      ((measure_mono hSubset).trans (by simp))
      zero_le
  have hAE : ∀ᵐ t ∂μ, t ≠ 0 := by
    have hz : μ {t : ℝ≥0 | t = 0} = 0 := by simpa using hZero
    simpa only [ae_iff, not_ne_iff] using hz
  change (∫ t, F t ∂μ) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [hAE] with t ht
  exact hF t ht
