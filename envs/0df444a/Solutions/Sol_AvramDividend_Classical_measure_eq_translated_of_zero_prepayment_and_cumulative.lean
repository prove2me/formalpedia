-- Prove2me | solution 1 for AvramDividend.Classical.measure_eq_translated_of_zero_prepayment_and_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:31:20.226146+00:00
-- url     : https://prove2.me/submissions/b5d08721-7904-4479-b25b-41db6f3aad4f

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ] (u : ℝ)
    (hμzero : μ (Set.Iic u) = 0)
    (hνzero : ν (Set.Iic (0 : ℝ)) = 0)
    (hcum : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioc u (u + t)) = ν (Set.Ioc (0 : ℝ) t)) :
    μ = Measure.map (fun t : ℝ => u + t) ν := by
  have red : ∀ (ρ : Measure ℝ) (c : ℝ), ρ (Iic c) = 0 → ∀ a b : ℝ,
      ρ (Ioc a b) = ρ (Ioc (max a c) b) := by
    intro ρ c h a b
    rw [← measure_inter_add_diff (Ioc a b) (measurableSet_Ioi : MeasurableSet (Ioi c))]
    have h0 : ρ (Ioc a b \ Ioi c) = 0 :=
      measure_mono_null (fun x hx => (not_lt.1 hx.2 : x ≤ c)) h
    rw [h0, add_zero, Set.Ioc_inter_Ioi]
  have shift : ∀ a' b' : ℝ, 0 ≤ a' → a' < b' → μ (Ioc (u + a') (u + b')) = ν (Ioc a' b') := by
    intro a' b' ha' hab
    have e1 : Ioc (u + a') (u + b') = Ioc u (u + b') \ Ioc u (u + a') := by
      ext x; simp only [Set.mem_Ioc, Set.mem_diff]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, fun h => by linarith [h.2]⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_not_ge fun h => h3 ⟨h1, h⟩, h2⟩
    have e2 : Ioc a' b' = Ioc 0 b' \ Ioc 0 a' := by
      ext x; simp only [Set.mem_Ioc, Set.mem_diff]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, fun h => by linarith [h.2]⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_not_ge fun h => h3 ⟨h1, h⟩, h2⟩
    have hs1 : Ioc u (u + a') ⊆ Ioc u (u + b') := Set.Ioc_subset_Ioc_right (by linarith)
    have hs2 : Ioc (0:ℝ) a' ⊆ Ioc 0 b' := Set.Ioc_subset_Ioc_right hab.le
    have hfin : μ (Ioc u (u + a')) ≠ ⊤ := measure_Ioc_lt_top.ne
    rw [e1, e2, measure_diff hs1 measurableSet_Ioc.nullMeasurableSet hfin,
      measure_diff hs2 measurableSet_Ioc.nullMeasurableSet (by rw [← hcum _ ha']; exact hfin),
      hcum _ ha', hcum _ (ha'.trans hab.le)]
  refine Measure.ext_of_Ioc μ _ fun a b hab => ?_
  rw [Measure.map_apply (measurable_const_add u) measurableSet_Ioc, Set.preimage_const_add_Ioc,
    red μ u hμzero, red ν 0 hνzero]
  have hm : max (a - u) 0 = max a u - u := by
    rcases le_total a u with h | h
    · rw [max_eq_right (by linarith), max_eq_right h, sub_self]
    · rw [max_eq_left (by linarith), max_eq_left h]
  rw [hm]
  rcases le_or_gt b (max a u) with hb | hb
  · rw [Set.Ioc_eq_empty_of_le hb, Set.Ioc_eq_empty_of_le (by linarith), measure_empty, measure_empty]
  · have := shift (max a u - u) (b - u) (by linarith [le_max_right a u]) (by linarith)
    simpa using this
