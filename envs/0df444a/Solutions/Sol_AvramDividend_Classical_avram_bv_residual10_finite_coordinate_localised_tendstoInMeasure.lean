-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_finite_coordinate_localised_tendstoInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:18:11.006076+00:00
-- url     : https://prove2.me/submissions/4e58ce83-3774-4303-a708-bd4e53b0b50f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact fixed-row original physical-grid coefficient localisation
converges in measure to its untruncated source, without any L1 claim. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i)) (f : Ω → ℝ) :
    TendstoInMeasure P
      (fun k : ℕ => fun ω : Ω =>
        if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
            abs (a z i) ≤ (k : ℝ)} then f ω else 0)
      atTop f := by
  let A : ℕ → Set Ω := fun k =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ (k : ℝ)}
  have hA : Tendsto (fun k : ℕ => P (A k)ᶜ) atTop (𝓝 (0 : ℝ≥0∞)) :=
    avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto n a ha
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hA (fun _ => bot_le) ?_
  intro k
  apply measure_mono
  intro ω hω
  by_cases hk : ω ∈ A k
  · simp only [Set.mem_setOf_eq] at hω
    split_ifs at hω with hc
    · have hzero : ε ≤ (0 : ℝ≥0∞) := by
        simpa only [edist_self] using hω
      exact False.elim ((not_le.mpr hε) hzero)
    · exact False.elim (hc hk)
  · exact hk
