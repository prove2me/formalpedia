-- Prove2me | solution 1 for BinaryQueryLB.fact_2_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:29:52.731174+00:00
-- url     : https://prove2.me/submissions/8adc05b0-80b7-4cbe-b322-fd8a03787112

import Mathlib

open MeasureTheory in
theorem solution (m : ℕ) (P : Set (EuclideanSpace ℝ (Fin m))) (hP : Bornology.IsBounded P) :
    MeasureTheory.volume (P ∩ ∅) = 0 ∧
      (∀ E : ℕ → Set (EuclideanSpace ℝ (Fin m)),
        (∀ k, MeasureTheory.NullMeasurableSet (E k) MeasureTheory.volume) →
        Pairwise (Function.onFun Disjoint E) →
          MeasureTheory.volume (P ∩ ⋃ k, E k) = ∑' k, MeasureTheory.volume (P ∩ E k)) ∧
      MeasureTheory.volume (P ∩ Set.univ) = MeasureTheory.volume P ∧
      MeasureTheory.volume P < ⊤ ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin m)), MeasureTheory.NullMeasurableSet E MeasureTheory.volume →
        MeasureTheory.volume (P ∩ E) ≤ MeasureTheory.volume E := by
  refine ⟨by rw [Set.inter_empty, measure_empty], fun E hE hdisj => ?_, by rw [Set.inter_univ],
    hP.measure_lt_top, fun E _ => measure_mono Set.inter_subset_right⟩
  have hE' : ∀ k, NullMeasurableSet (E k) (volume.restrict P) :=
    fun k => (hE k).mono Measure.restrict_le_self
  have hU : NullMeasurableSet (⋃ k, E k) (volume.restrict P) := NullMeasurableSet.iUnion hE'
  have h := measure_iUnion₀ (μ := volume.restrict P) (fun i j hij => (hdisj hij).aedisjoint) hE'
  rw [Measure.restrict_apply₀ hU] at h
  rw [Set.inter_comm, h]
  refine tsum_congr fun k => ?_
  rw [Measure.restrict_apply₀ (hE' k), Set.inter_comm]
