-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a130_true_original_gaussian_lastcell_remove_positive_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:07:14.154322+00:00
-- url     : https://prove2.me/submissions/f99ec2b4-41a8-4d76-88ae-d78973352650

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

/-- One integrable original Gaussian terminal source error may be removed from an integrable positive spatial residual. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A Last : Ω → ℝ)
    (hMeas : AEStronglyMeasurable (fun ω => max (A ω) 0) P)
    (hSum : Integrable (fun ω => max (A ω + Last ω) 0) P)
    (hLast : Integrable (fun ω => |Last ω|) P) :
    Integrable (fun ω => max (A ω) 0) P := by
  apply Integrable.mono' (hSum.add hLast) hMeas
  filter_upwards [] with ω
  change ‖max (A ω) 0‖ ≤ max (A ω + Last ω) 0 + |Last ω|
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (A ω) 0)]
  apply max_le
  · linarith [le_max_left (A ω + Last ω) 0, neg_le_abs (Last ω)]
  · linarith [le_max_right (A ω + Last ω) 0, abs_nonneg (Last ω)]
