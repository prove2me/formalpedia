-- Prove2me | solution 1 for FamousTheorems.caratheodory_criterion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:27:03.588509+00:00
-- url     : https://prove2.me/submissions/6f0013e0-8c0f-4ae3-85e2-c5e8e093882e

import Mathlib

open scoped MeasureTheory

theorem solution {α : Type*} (m : MeasureTheory.OuterMeasure α) :
    (∀ s : Set α, MeasurableSet[m.caratheodory] s ↔ ∀ t, m t = m (t ∩ s) + m (t \ s)) ∧
      ∀ s : ℕ → Set α, (∀ i, MeasurableSet[m.caratheodory] (s i)) → Pairwise (Function.onFun Disjoint s) →
        m (⋃ i, s i) = ∑' i, m (s i) :=
  ⟨fun _ => m.isCaratheodory_iff, fun _ hs hd => m.iUnion_eq_of_caratheodory hs hd⟩
