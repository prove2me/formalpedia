-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_abs_L1_global_to_restricted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:26:43.060674+00:00
-- url     : https://prove2.me/submissions/47b4dc74-e1bf-4dae-bafc-c58b68b9905f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (B : ℕ → Ω → ℝ)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
       atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω => |B m ω|) (P.restrict A)) ∧
    Tendsto (fun m => ∫ ω in A, |B m ω| ∂P)
       atTop (𝓝 (0 : ℝ)) := by
  constructor
  · exact fun m => (hBI m).mono_measure Measure.restrict_le_self
  · have h0 (m : ℕ) : 0 ≤ ∫ ω in A, |B m ω| ∂P :=
      integral_nonneg (fun ω => abs_nonneg _)
    have h1 (m : ℕ) :
        (∫ ω in A, |B m ω| ∂P) ≤ (∫ ω, |B m ω| ∂P) :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun ω => abs_nonneg _)) (hBI m)
    exact squeeze_zero h0 h1 hBt
