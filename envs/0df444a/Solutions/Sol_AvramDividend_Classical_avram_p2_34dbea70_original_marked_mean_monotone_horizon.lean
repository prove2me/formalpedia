-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_monotone_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:42:31.602213+00:00
-- url     : https://prove2.me/submissions/a1f59713-0714-4ad5-b787-8088625a030e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original intrinsic marked-jump expected counts increase with the horizon. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T S : ℝ≥0) (hTS : T ≤ S) (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 S ×ˢ B) ∂P) := by
  apply lintegral_mono
  intro ω
  apply MeasureTheory.measure_mono
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans hTS⟩, hp.2⟩
