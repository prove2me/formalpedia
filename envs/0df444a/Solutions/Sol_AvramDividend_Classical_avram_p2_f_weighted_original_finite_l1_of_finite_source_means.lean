-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_finite_l1_of_finite_source_means
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:15:38.115633+00:00
-- url     : https://prove2.me/submissions/067fc5ea-bbe1-4633-96fd-c7825d2d0143

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original marked-count weighted first moment is finite
whenever both original unweighted first moments are finite. -/
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
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hNfinite : (∫⁻ ω, N ω ∂P) ≠ ∞) :
    (∫⁻ ω, H ω * N ω ∂P) ≠ ∞ := by
  have hFun :
      N = fun ω => ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B) := by
    funext ω
    exact hSource ω
  have hFact :
      (∫⁻ ω, H ω * N ω ∂P) =
      (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P) := by
    rw [hFun]
    exact avram_p2_f_weighted_original_intrinsic_future_past_product
      X s T B hB H hH
  rw [hFact]
  exact ENNReal.mul_ne_top hHfinite hNfinite
