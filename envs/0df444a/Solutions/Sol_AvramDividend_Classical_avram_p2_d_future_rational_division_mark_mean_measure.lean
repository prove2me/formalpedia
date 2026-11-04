-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_rational_division_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:57:38.388186+00:00
-- url     : https://prove2.me/submissions/75a7b29b-0e19-4309-b21d-fc7d9a7f181f

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_rational_time_uniform_mark_mean_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- At every literal nonnegative rational horizon n/d, one source mark
measure gives the exact expected marked jump rate with no ν identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ, ∀ (n d : ℕ), 0 < d →
      ∀ (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 ((n : ℝ≥0) / (d : ℝ≥0)) ×ˢ B) ∂P) =
        ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * ρ B := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_rational_time_uniform_mark_mean_measure X
  refine ⟨ρ, ?_⟩
  intro n d hd B hB
  have hdNN : (d : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hrel : (d : ℝ≥0) * ((n : ℝ≥0) / (d : ℝ≥0)) =
      (n : ℝ≥0) := by
    field_simp [hdNN]
  exact hρ ((n : ℝ≥0) / (d : ℝ≥0)) n d hd hrel B hB
