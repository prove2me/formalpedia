-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_left_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:16:48.831382+00:00
-- url     : https://prove2.me/submissions/520c4527-da71-4f23-aa4c-72aec7640f61

import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

/-- The far-left tail of a finite real Borel measure vanishes as the
cutoff tends to minus infinity. -/
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => μ (Iic (-(n : ℝ)))) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => Iic (-(n : ℝ))) := by
    intro i j hij x hx
    change x ≤ -(j : ℝ) at hx
    change x ≤ -(i : ℝ)
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hinter : (⋂ n : ℕ, Iic (-(n : ℝ))) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    have hxn := hx n
    linarith
  have h := tendsto_measure_iInter_atTop
    (μ := μ) (s := fun n : ℕ => Iic (-(n : ℝ)))
    (fun n => (measurableSet_Iic : MeasurableSet (Iic (-(n : ℝ)))).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  simpa [hinter, Function.comp_def] using h
