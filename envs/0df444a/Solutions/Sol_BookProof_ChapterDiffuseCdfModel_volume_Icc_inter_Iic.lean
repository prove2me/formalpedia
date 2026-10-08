-- Prove2me | solution 1 for BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:50.286982+00:00
-- url     : https://prove2.me/submissions/2b7964f2-7d00-463e-baa0-e13fbd3419e6

-- Generated from ChapterDiffuseCdfModel.lean — solution of BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
open BookProof.ChapterDiffuseCdfModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

variable (mu : Measure ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {t : ℝ} (ht1 : t ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) = ENNReal.ofReal t := by

  rw [Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [hset, Real.volume_Icc]
  simp
