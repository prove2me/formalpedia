-- Prove2me | solution 1 for AvramDividend.Classical.measure_eq_of_positive_cumulative_and_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:30:29.667134+00:00
-- url     : https://prove2.me/submissions/69be39b0-d5b6-4ae3-ae0e-b3123cd1495e

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (hμ : μ (Set.Iic (0 : ℝ)) = 0)
    (hν : ν (Set.Iic (0 : ℝ)) = 0)
    (hcdf : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioc (0 : ℝ) t) = ν (Set.Ioc (0 : ℝ) t)) :
    μ = ν := by
  have red : ∀ ρ : Measure ℝ, ρ (Iic 0) = 0 → ∀ a b : ℝ,
      ρ (Ioc a b) = ρ (Ioc (max a 0) b) := by
    intro ρ h a b
    rw [← measure_inter_add_diff (Ioc a b) (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))]
    have h0 : ρ (Ioc a b \ Ioi 0) = 0 :=
      measure_mono_null (fun x hx => (not_lt.1 hx.2 : x ≤ 0)) h
    rw [h0, add_zero, Set.Ioc_inter_Ioi]

  refine Measure.ext_of_Ioc μ ν fun a b hab => ?_
  rw [red μ hμ, red ν hν]
  rcases le_or_gt b (max a 0) with hb | hb
  · simp [Set.Ioc_eq_empty_of_le hb]
  · have ha0 : 0 ≤ max a 0 := le_max_right _ _
    have hsub : Ioc 0 (max a 0) ⊆ Ioc 0 b := Set.Ioc_subset_Ioc_right hb.le
    have e : Ioc (max a 0) b = Ioc 0 b \ Ioc 0 (max a 0) := by
      ext x; simp only [Set.mem_Ioc, Set.mem_diff]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_le_of_lt ha0 h1, h2⟩, fun h => absurd h.2 (not_le.2 h1)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_not_ge fun h => h3 ⟨h1, h⟩, h2⟩
    have hfin : μ (Ioc 0 (max a 0)) ≠ ⊤ := measure_Ioc_lt_top.ne
    rw [e, measure_diff hsub measurableSet_Ioc.nullMeasurableSet hfin,
      measure_diff hsub measurableSet_Ioc.nullMeasurableSet (by rw [← hcdf _ ha0]; exact hfin),
      hcdf _ ha0, hcdf _ (ha0.trans hb.le)]
