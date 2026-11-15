-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_cadlag_equal_jump_cancellation_regular_residual_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:14:46.382977+00:00
-- url     : https://prove2.me/submissions/23be6844-4c73-4f0c-9813-2e20af8c1298

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Cancelling the exact left jumps of two cadlag paths yields an all-path continuous-from-right zero-jump residual. -/
theorem solution
    (f J : ℝ≥0 → ℝ)
    (hfRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hJRight : ∀ t : ℝ≥0, ContinuousWithinAt J (Ici t) t)
    (hfLeft : ∀ t : ℝ≥0, 0 < t →
      Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    (hJLeft : ∀ t : ℝ≥0, 0 < t →
      Tendsto J (𝓝[<] t) (𝓝 (Function.leftLim J t)))
    (hMatch : ∀ t : ℝ≥0, 0 < t →
      f t - Function.leftLim f t = J t - Function.leftLim J t) :
    (∀ t : ℝ≥0, ContinuousWithinAt (fun u => f u - J u) (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t →
      ∃ l, Tendsto (fun u => f u - J u) (𝓝[<] t) (𝓝 l)) ∧
    (∀ t l, 0 < t →
      Tendsto (fun u => f u - J u) (𝓝[<] t) (𝓝 l) →
      f t - J t ≤ l) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (hfRight t).sub (hJRight t)
  · intro t ht
    exact ⟨Function.leftLim f t - Function.leftLim J t,
      (hfLeft t ht).sub (hJLeft t ht)⟩
  · intro t l ht hLim
    haveI : NeBot (𝓝[<] t) :=
      nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    have hCanonical : Tendsto (fun u => f u - J u) (𝓝[<] t)
        (𝓝 (Function.leftLim f t - Function.leftLim J t)) :=
      (hfLeft t ht).sub (hJLeft t ht)
    have hUnique : l = Function.leftLim f t - Function.leftLim J t :=
      tendsto_nhds_unique hLim hCanonical
    have hEqual : f t - J t =
        Function.leftLim f t - Function.leftLim J t := by
      linarith [hMatch t ht]
    rw [hUnique]
    exact le_of_eq hEqual
