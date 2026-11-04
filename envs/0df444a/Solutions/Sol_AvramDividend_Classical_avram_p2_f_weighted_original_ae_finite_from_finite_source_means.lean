-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_ae_finite_from_finite_source_means
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:40:59.567196+00:00
-- url     : https://prove2.me/submissions/724cc703-6dc0-43d1-90ae-40fba9f10c9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_l1_of_finite_source_means

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The source-original weighted jump rectangle count is finite almost
surely when its two independent first moments are finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H N : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (hSource : ∀ ω : Ω, N ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s (s + T) ×ˢ B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hNfinite : (∫⁻ ω, N ω ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, H ω * N ω < ∞ := by
  have hFun :
      N = fun ω => ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s (s + T) ×ˢ B) := by
    funext ω
    exact hSource ω
  have hNmeas : Measurable N := by
    rw [hFun]
    exact avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X s T B hB
  have hHmeas : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  exact MeasureTheory.ae_lt_top (hHmeas.mul hNmeas)
    (avram_p2_f_weighted_original_finite_l1_of_finite_source_means
      X s T B hB H N hH hSource hHfinite hNfinite)
