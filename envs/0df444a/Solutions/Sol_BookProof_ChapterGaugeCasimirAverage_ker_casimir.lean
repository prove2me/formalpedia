-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.ker_casimir
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:24:59.120007+00:00
-- url     : https://prove2.me/submissions/b9238fe3-dea3-4388-801e-5bb154ca2103

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.ker_casimir
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
import Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_casimir_apply_eq_zero_iff
open BookProof.ChapterGaugeCasimirAverage




open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric) :
    LinearMap.ker (casimir T) = ⨅ a, LinearMap.ker (T a) := by

  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  exact casimir_apply_eq_zero_iff T hT v
