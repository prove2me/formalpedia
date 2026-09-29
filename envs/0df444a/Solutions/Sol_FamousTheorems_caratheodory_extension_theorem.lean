-- Prove2me | solution 1 for FamousTheorems.caratheodory_extension_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:42:56.28942+00:00
-- url     : https://prove2.me/submissions/b8cdf418-f0f9-4466-bd08-c98a6119411d

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [mα : MeasurableSpace α] {C : Set (Set α)} (m : AddContent ENNReal C)
    (hC : IsSetSemiring C) (hC_gen : mα = MeasurableSpace.generateFrom C) (hm : m.IsSigmaSubadditive) :
    ∃ μ : Measure α, ∀ s ∈ C, μ s = m s :=
  ⟨_, fun _ hs => m.measure_eq hC hC_gen hm hs⟩
