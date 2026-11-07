-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_positive_error_moving_event_tail_absorption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:05:58.855223+00:00
-- url     : https://prove2.me/submissions/f1daf1c4-6f27-47c1-9286-37461d9785b6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_measurable_event_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Classical
noncomputable section

/-- The original positive-error mean vanishes when both the moving interior
localisation and its complementary terminal/boundary tail vanish in mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (s : ℕ → Set Ω) (hs : ∀ m, MeasurableSet (s m))
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hLocal : Tendsto
      (fun m => ∫ ω, max (if ω ∈ s m then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hTail : Tendsto
      (fun m => ∫ ω, max (if ω ∉ s m then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hSplit (m : ℕ) :
      (∫ ω, max (Err m ω) 0 ∂P) =
        (∫ ω, max (if ω ∈ s m then Err m ω else 0) 0 ∂P) +
        (∫ ω, max (if ω ∉ s m then Err m ω else 0) 0 ∂P) :=
    (avram_bv_error7_positive_error_measurable_event_split
      P (s m) (hs m) (Err m) (hPos m)).2.2
  have hEq :
      (fun m => ∫ ω, max (Err m ω) 0 ∂P) =
      (fun m =>
        (∫ ω, max (if ω ∈ s m then Err m ω else 0) 0 ∂P) +
        (∫ ω, max (if ω ∉ s m then Err m ω else 0) 0 ∂P)) := by
    funext m
    exact hSplit m
  rw [hEq]
  simpa using hLocal.add hTail
