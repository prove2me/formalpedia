-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.memLp_top_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:37:15.281392+00:00
-- url     : https://prove2.me/submissions/64a245ab-33fb-4836-818a-e6e6d6bad12a

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.memLp_top_conj
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) :
    MemLp (fun x => (starRingEnd ℂ) (φ x)) ⊤ μ := by

  refine ⟨hφ.aestronglyMeasurable.star, ?_⟩
  have hnorm : eLpNorm (fun x => (starRingEnd ℂ) (φ x)) ⊤ μ = eLpNorm φ ⊤ μ := by
    simp [eLpNorm_exponent_top, eLpNormEssSup]
  rw [hnorm]
  exact hφ.eLpNorm_lt_top
