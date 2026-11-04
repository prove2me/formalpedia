-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_subinterval_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:11:07.949554+00:00
-- url     : https://prove2.me/submissions/ed32129d-827a-4e6c-a721-5fe9404d462d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Split the original intrinsic marked mean at any ordered deterministic time. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ B) ∂P) +
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (t - s) ×ˢ B) ∂P) := by
  let F : ℝ≥0 → ℝ≥0∞ := fun u =>
    ∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
      X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 =>
        (v, X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc 0 u ×ˢ B) ∂P
  change F t = F s + F (t - s)
  have hadd :=
    avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis
      X s (t - s) B hB
  have hs : s + (t - s) = t := add_tsub_cancel_of_le hst
  simpa only [hs] using hadd
