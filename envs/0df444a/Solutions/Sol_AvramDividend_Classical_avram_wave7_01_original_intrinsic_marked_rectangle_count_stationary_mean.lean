-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:09:05.911262+00:00
-- url     : https://prove2.me/submissions/07a3d9b1-b521-4fa6-bc42-1030aa592a8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original intrinsic marked jump count has stationary expected increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) := by
  classical
  let N (r : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc r (r + T) ×ˢ B)
  let Y (r : ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ :=
    fun t => X.X (r + t) ω - X.X r ω
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable T B hB
  have hPath (r : ℝ≥0) (ω : Ω) : N r ω = F (Y r ω) := by
    have hCount :=
      avram_wave5_01_actual_source_futurepath_marked_count_transport
        X ω r T B hB
    have hReg :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag X ω r
    exact hCount.trans (hExtract (Y r ω) hReg.1 hReg.2)
  let Z : Ω → (ℝ≥0 → ℝ) := fun ζ t => X.X t ζ
  have hTest :
      Measurable (fun p : Unit × (ℝ≥0 → ℝ) => F p.2) :=
    hF.comp measurable_snd
  have hKernel (r : ℝ≥0) :
      (∫⁻ ω, F (Y r ω) ∂P) =
      (∫⁻ ω, (∫⁻ y, F y ∂(Measure.map Z P)) ∂P) := by
    have h :=
      avram_root29_01_original_future_kernel_past_test
        X r (fun _ : Ω => ())
        (measurable_const : Measurable[𝓕 r] (fun _ : Ω => ()))
        Set.univ (MeasurableSet.univ)
        (fun p : Unit × (ℝ≥0 → ℝ) => F p.2) hTest
    simpa [Y, Z] using h
  have hMain :
      (∫⁻ ω, N s ω ∂P) = (∫⁻ ω, N 0 ω ∂P) := by
    calc
      (∫⁻ ω, N s ω ∂P) = ∫⁻ ω, F (Y s ω) ∂P := by
        apply lintegral_congr
        intro ω
        exact hPath s ω
      _ = ∫⁻ ω, F (Y 0 ω) ∂P :=
        (hKernel s).trans (hKernel 0).symm
      _ = ∫⁻ ω, N 0 ω ∂P := by
        apply lintegral_congr
        intro ω
        exact (hPath 0 ω).symm
  simpa only [N, zero_add] using hMain
