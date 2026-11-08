-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:36:17.586935+00:00
-- url     : https://prove2.me/submissions/987f47bb-bb50-4ddc-b51c-4e654b593ad2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-coordinate clipping events for an original physical grid exhaust a
finite measure in probability, with no continuity-of-path assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i)) :
    Tendsto (fun k : ℕ =>
      P ({ω : Ω | ∀ i ∈ Finset.range (n + 1),
        abs (a ω i) ≤ (k : ℝ)}ᶜ)) atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let A : ℕ → Set Ω := fun k =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ (k : ℝ)}
  have hAm (k : ℕ) : MeasurableSet (A k) :=
    avram_bv_residual10_finite_coordinate_event_measurable n a ha k
  have hanti : Antitone (fun k : ℕ => (A k)ᶜ) := by
    intro k l hkl
    apply Set.compl_subset_compl.mpr
    intro ω hω i hi
    exact (hω i hi).trans (by exact_mod_cast hkl)
  have hEmpty : (⋂ k : ℕ, (A k)ᶜ) = (∅ : Set Ω) := by
    ext ω
    constructor
    · intro hω
      obtain ⟨N, hN⟩ :=
        avram_bv_residual10_finite_coordinate_event_exhaustion n a ω
      have hnot : ω ∉ A N := Set.mem_iInter.mp hω N
      exact hnot (hN N le_rfl)
    · intro hω
      simp at hω
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (s := fun k : ℕ => (A k)ᶜ)
    (fun k => (hAm k).compl.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hEmpty, measure_empty] at hlim
  exact hlim
