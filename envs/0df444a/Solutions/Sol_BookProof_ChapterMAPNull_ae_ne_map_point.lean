-- Prove2me | solution 1 for BookProof.ChapterMAPNull.ae_ne_map_point
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:27:42.567952+00:00
-- url     : https://prove2.me/submissions/f0071c02-e5a0-4474-837e-89fe9c069e14

-- Generated from ChapterMAPNull.lean — solution of BookProof.ChapterMAPNull.ae_ne_map_point
import Mathlib
import Definitions.Def_ChapterMAPNull
import Theorems.Thm_BookProof_ChapterMAPNull_map_point_measure_zero
open BookProof.ChapterMAPNull



open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) :
    ∀ᵐ x ∂μ, x ≠ mapPoint := by

  convert MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
    ( map_point_measure_zero μ mapPoint ) using 1
  · funext x; simp
