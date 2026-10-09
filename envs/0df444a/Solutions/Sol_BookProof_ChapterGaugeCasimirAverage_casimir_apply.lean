-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.casimir_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:24:44.637376+00:00
-- url     : https://prove2.me/submissions/e5e3afa7-c1cd-4060-8cc7-15c665867fb5

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.casimir_apply
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
open BookProof.ChapterGaugeCasimirAverage




open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (T : ι → V →ₗ[ℂ] V) (v : V) :
    casimir T v = ∑ a, T a (T a v) := by

  simp [casimir, LinearMap.sum_apply]
