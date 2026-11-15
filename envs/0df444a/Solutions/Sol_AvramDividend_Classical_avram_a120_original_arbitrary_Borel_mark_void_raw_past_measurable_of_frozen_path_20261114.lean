-- Prove2me | solution 1 for AvramDividend.Classical.avram_a120_original_arbitrary_Borel_mark_void_raw_past_measurable_of_frozen_path_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:27:08.583825+00:00
-- url     : https://prove2.me/submissions/28ef7135-ab50-41bf-8fe8-f8d74ff0cd3d

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
    (T : ℝ≥0) (B : Set ℝ)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFrozen : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (min v T) ω)) :
    MeasurableSet[𝓕 T]
      {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
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
      {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} =
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (min v T) ω)) ⁻¹'
        ({0} : Set ℝ≥0∞) := by
    ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      hFrozen ω]
  rw [hEvent]
  exact (measurableSet_singleton (0 : ℝ≥0∞)).preimage (hF.comp hPath)

-- W7-06 snapshot validation refresh variant 2; mathematical proof unchanged.
