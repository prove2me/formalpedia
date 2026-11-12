-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb59_finite_L2_MDS_zero_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:13:27.071148+00:00
-- url     : https://prove2.me/submissions/40bb9751-04c3-4163-bb80-eff8a8f6ebb9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal

/-- Extend a finite discrete L2 martingale-difference family by zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (𝓖 : Filtration ℕ mΩ)
    (m : ℕ) (U : ℕ → Ω → ℝ)
    (hL2 : ∀ i, i ≤ m → MemLp (U i) 2 P)
    (hadapt : ∀ i, i ≤ m → StronglyMeasurable[𝓖 (i + 1)] (U i))
    (hcentred : ∀ i, i ≤ m → P[U i | 𝓖 i] =ᵐ[P] (fun _ => 0)) :
    let V : ℕ → Ω → ℝ := fun i => if i ≤ m then U i else fun _ => 0
    (∀ i, MemLp (V i) 2 P) ∧
    (∀ i, StronglyMeasurable[𝓖 (i + 1)] (V i)) ∧
    (∀ i, P[V i | 𝓖 i] =ᵐ[P] (fun _ => 0)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ≤ m
    · simpa only [if_pos hi] using hL2 i hi
    · simp [hi]
  · intro i
    by_cases hi : i ≤ m
    · simpa only [if_pos hi] using hadapt i hi
    · simpa only [if_neg hi] using
        (stronglyMeasurable_const :
          StronglyMeasurable[𝓖 (i + 1)] (fun _ : Ω => (0 : ℝ)))
  · intro i
    by_cases hi : i ≤ m
    · simpa only [if_pos hi] using hcentred i hi
    · simp [hi]
