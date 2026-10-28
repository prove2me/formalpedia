-- Prove2me | solution 1 for AvramDividend.Classical.measure_eq_map_add_of_all_Ioc_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:05:59.560693+00:00
-- url     : https://prove2.me/submissions/6ce4390e-f697-4048-958a-6d89978c6467

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Equality of interval masses after time translation determines
    the entire pushforward measure, allowing weighted integrals to shift. -/
theorem solution
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (u : ℝ)
    (hshift : ∀ a b : ℝ, a < b →
      μ (Set.Ioc (u + a) (u + b)) = ν (Set.Ioc a b)) :
    μ = Measure.map (fun t : ℝ => u + t) ν := by
  have hm : Measurable (fun t : ℝ => u + t) :=
    measurable_const.add measurable_id
  apply Measure.ext_of_Ioc μ (Measure.map (fun t : ℝ => u + t) ν)
  intro a b hab
  have hpre :
      (fun t : ℝ => u + t) ⁻¹' Set.Ioc a b =
        Set.Ioc (a - u) (b - u) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
  rw [Measure.map_apply hm (measurableSet_Ioc), hpre]
  have heq := hshift (a - u) (b - u) (by linarith)
  have hleft : u + (a - u) = a := by ring
  have hright : u + (b - u) = b := by ring
  simpa only [hleft, hright] using heq
