-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:36:50.807203+00:00
-- url     : https://prove2.me/submissions/8a91cae7-e87c-4969-afec-c7476ce67611

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_void_stationary_of_shared_path_counter

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
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0} =
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
  classical
  obtain ⟨F, hMeasF, hCountF⟩ :=
    avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable T B hB
  have hClockRep : ∀ (r : ℝ≥0) (ω : Ω),
      NX ω (Ioc r (r + T) ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (r + v) ω - X.X r ω) := by
    intro r ω
    have hCadlag :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag X ω r
    have hTime :=
      avram_wave5_01_actual_source_futurepath_marked_count_transport
        X ω r T B hB
    rw [hNX ω]
    exact hTime.trans (hCountF _ hCadlag.1 hCadlag.2)
  have hFuture : ∀ ω : Ω,
      NX ω (Ioc s (s + T) ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by
    intro ω
    exact hClockRep s ω
  have hOrigin : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X v ω) := by
    intro ω
    simpa only [zero_add, X.X_zero, sub_zero] using hClockRep 0 ω
  exact
    avram_wave7_06_original_intrinsic_marked_void_stationary_of_shared_path_counter
      X NX hNX s T B hB F hMeasF hFuture hOrigin
