-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_void_stationary_of_shared_path_counter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:42:15.665252+00:00
-- url     : https://prove2.me/submissions/39386d27-788a-468a-820e-9ab717e1fb05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original marked-jump void stationarity from the common measurable
functional of the same original shifted and unshifted Lévy paths. -/
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
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFuture : ∀ ω : Ω,
      NX ω (Ioc s (s + T) ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (hOrigin : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X v ω)) :
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0} =
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
  have hZero : MeasurableSet
      {Y : ℝ≥0 → ℝ | F Y = 0} :=
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage hF
  have hShift :
      Measurable (fun ω : Ω =>
        fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) :=
    avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X s
  have hOrig : Measurable (fun ω : Ω =>
      fun v : ℝ≥0 => X.X v ω) := levy_wholePath_measurable X
  have hLaw : Measure.map (fun ω : Ω =>
        fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) P =
      Measure.map (fun ω : Ω =>
        fun v : ℝ≥0 => X.X v ω) P :=
    levy_shiftedFuturePath_stationary_law X s
  have hEvent : P {ω : Ω |
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) = 0} =
      P {ω : Ω | F (fun v : ℝ≥0 => X.X v ω) = 0} := by
    calc
      P {ω : Ω |
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) = 0} =
          (Measure.map (fun ω : Ω =>
            fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) P)
              {Y : ℝ≥0 → ℝ | F Y = 0} := by
                rw [Measure.map_apply hShift hZero]
                rfl
      _ = (Measure.map (fun ω : Ω => fun v : ℝ≥0 => X.X v ω) P)
              {Y : ℝ≥0 → ℝ | F Y = 0} := by rw [hLaw]
      _ = P {ω : Ω | F (fun v : ℝ≥0 => X.X v ω) = 0} := by
            rw [Measure.map_apply hOrig hZero]
            rfl
  calc
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0} =
      P {ω : Ω | F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) = 0} := by
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, hFuture ω]
    _ = P {ω : Ω | F (fun v : ℝ≥0 => X.X v ω) = 0} := hEvent
    _ = P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, hOrigin ω]
