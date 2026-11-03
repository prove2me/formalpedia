-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_past_measurable_of_frozen_source_rep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:49:08.451177+00:00
-- url     : https://prove2.me/submissions/0d24e2df-1e1a-4d91-b3e8-74a2af1f14b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T : ℝ≥0) (n : ℕ)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFrozen : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
        F (fun v : ℝ≥0 => X.X (min v T) ω)) :
    MeasurableSet[𝓕 T]
      {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
  classical
  have hCoordinate (v : ℝ≥0) :
      Measurable[𝓕 T] (fun ω : Ω => X.X (min v T) ω) := by
    exact (X.adapted (min v T)).mono
      (𝓕.mono (min_le_right v T)) le_rfl
  have hPath :
      Measurable[𝓕 T]
        (fun ω : Ω => (fun v : ℝ≥0 => X.X (min v T) ω)) := by
    letI : MeasurableSpace Ω := 𝓕 T
    exact measurable_pi_iff.mpr hCoordinate
  have hEvent :
      {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (min v T) ω)) ⁻¹'
        ({0} : Set ℝ≥0∞) := by
    ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      hFrozen ω]
  rw [hEvent]
  exact (measurableSet_singleton (0 : ℝ≥0∞)).preimage (hF.comp hPath)

-- W7-06 snapshot validation refresh variant 2; mathematical proof unchanged.
