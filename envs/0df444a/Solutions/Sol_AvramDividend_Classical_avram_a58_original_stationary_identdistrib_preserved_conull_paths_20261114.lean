-- Prove2me | solution 1 for AvramDividend.Classical.avram_a58_original_stationary_identdistrib_preserved_conull_paths_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:22:38.601825+00:00
-- url     : https://prove2.me/submissions/5523af83-9163-486e-b608-4c73648c62d2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Stationary source increments survive simultaneous conull all-time modification on the same probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t, F t ω = G t ω)
    (hMeas : ∀ t, Measurable (G t))
    (hStat : ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => F t ω - F s ω) (F (t - s)) P P) :
    ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P := by
  intro s t hst
  have hL : (fun ω => G t ω - G s ω) =ᵐ[P]
      (fun ω => F t ω - F s ω) := by
    filter_upwards [hEq] with ω heq
    rw [← heq t, ← heq s]
  have hR : (G (t - s)) =ᵐ[P] (F (t - s)) := by
    filter_upwards [hEq] with ω heq
    exact (heq (t - s)).symm
  refine ⟨((hMeas t).sub (hMeas s)).aemeasurable,
    (hMeas (t - s)).aemeasurable, ?_⟩
  calc
    Measure.map (fun ω => G t ω - G s ω) P =
        Measure.map (fun ω => F t ω - F s ω) P :=
      Measure.map_congr hL
    _ = Measure.map (F (t - s)) P :=
      (hStat s t hst).map_eq
    _ = Measure.map (G (t - s)) P :=
      (Measure.map_congr hR).symm
