-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a531_finite_sum_positive_parts_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:30:59.722216+00:00
-- url     : https://prove2.me/submissions/b60b163d-895a-455e-beb4-8c98ba4cda59

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hMeas : ∀ i ∈ S, AEStronglyMeasurable (f i) P)
    (hPos : ∀ i ∈ S, Integrable (fun ω => max (f i ω) (0 : ℝ)) P) :
    Integrable (fun ω => max (∑ i ∈ S, f i ω) (0 : ℝ)) P := by
  classical
  have hI : Integrable
      (fun ω => ∑ i ∈ S, max (f i ω) (0 : ℝ)) P :=
    integrable_finset_sum S (fun i hi => hPos i hi)
  have hm : AEStronglyMeasurable
      (fun ω => max (∑ i ∈ S, f i ω) (0 : ℝ)) P := by
    have hs : AEStronglyMeasurable (fun ω => ∑ i ∈ S, f i ω) P :=
      Finset.aestronglyMeasurable_fun_sum S (fun i hi => hMeas i hi)
    exact (hs.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  apply hI.mono_nonneg hm
    (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  filter_upwards with ω
  apply max_le
  · apply Finset.sum_le_sum
    intro i hi
    exact le_max_left _ _
  · exact Finset.sum_nonneg fun i hi => le_max_right _ _
