-- Prove2me | solution 1 for BookProof.ChapterG2.haarAverage_invariant
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:56:36.788503+00:00
-- url     : https://prove2.me/submissions/9991ed82-2b8b-4966-a8e5-81301dda53b6

import Definitions.Def_ChapterG2
import Definitions.Def_ChapterG

open BookProof.ChapterG
open BookProof.ChapterG2

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem solution [MeasurableMul G] (f : X → ℝ) (g : G) (x : X) :
    haarAverage (μG := μG) f (g • x) = haarAverage (μG := μG) f x := by
  simpa only [haarAverage, mul_inv_rev, mul_smul, inv_inv, inv_mul_cancel_left] using
    integral_mul_left_eq_self (μ := μG) (fun h : G => f (h⁻¹ • x)) g⁻¹
