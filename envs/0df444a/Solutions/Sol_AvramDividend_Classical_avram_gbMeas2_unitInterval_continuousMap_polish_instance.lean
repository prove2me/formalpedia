-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbMeas2_unitInterval_continuousMap_polish_instance
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:01:01.07638+00:00
-- url     : https://prove2.me/submissions/788125d6-d9a0-4ec0-b892-6aca0458225a

import Mathlib
open MeasureTheory
noncomputable section
theorem solution :
    PolishSpace C(unitInterval, ℝ) := by infer_instance
