-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:48:44.149996+00:00
-- url     : https://prove2.me/submissions/23dbecce-7aee-485f-b093-b8db40cd6946

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (g : ℝ≥0∞ → ℝ) (hg : Measurable g)
    (hOrigin : Integrable
      (fun ω => g (NX ω (Ioc 0 T ×ˢ B))) P) :
    Integrable (fun ω => g (NX ω (Ioc s (s + T) ×ˢ B))) P ∧
    (∫ ω, g (NX ω (Ioc s (s + T) ×ˢ B)) ∂P) =
      ∫ ω, g (NX ω (Ioc 0 T ×ˢ B)) ∂P := by
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
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (s + t) ω - X.X s ω
  let W : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hZm : Measurable Z := by
    exact measurable_pi_lambda _ fun t =>
      (X.adapted.measurable (i := s + t)).sub
        (X.adapted.measurable (i := s))
  have hWm : Measurable W := levy_wholePath_measurable X
  have hFutureEq :
      (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) = F ∘ Z := by
    funext ω
    exact hClockRep s ω
  have hOriginEq :
      (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) = F ∘ W := by
    funext ω
    simpa only [W, Function.comp_apply, zero_add, X.X_zero, sub_zero]
      using hClockRep 0 ω
  have hFutureM :
      Measurable (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) := by
    rw [hFutureEq]
    exact hMeasF.comp hZm
  have hOriginM :
      Measurable (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) := by
    rw [hOriginEq]
    exact hMeasF.comp hWm
  have hLaw :
      IdentDistrib
        (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B))
        (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) P P := by
    refine ⟨hFutureM.aemeasurable, hOriginM.aemeasurable, ?_⟩
    exact avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
      X NX hNX s T B hB
  have hG := hLaw.comp hg
  constructor
  · exact hG.integrable_iff.mpr hOrigin
  · exact hG.integral_eq
