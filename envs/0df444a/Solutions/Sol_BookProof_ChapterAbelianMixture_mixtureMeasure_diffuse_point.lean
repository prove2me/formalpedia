-- Prove2me | solution 1 for BookProof.ChapterAbelianMixture.mixtureMeasure_diffuse_point
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:49.541811+00:00
-- url     : https://prove2.me/submissions/8d4e4999-96aa-4447-9126-1042114e10b5

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.mixtureMeasure_diffuse_point
import Mathlib
import Definitions.Def_ChapterAbelianMixture
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal

namespace BookProof.ChapterAbelianMixture
end BookProof.ChapterAbelianMixture

theorem solution {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    mixtureMeasure {x} = 0 := by
  have hx2 : x ≠ 2 := by
    rcases hx with ⟨_, hx1⟩
    intro h; rw [h] at hx1; norm_num at hx1
  have hv : MeasureTheory.volume ({x} ∩ Set.Icc (0 : ℝ) 1) = 0 :=
    measure_mono_null Set.inter_subset_left (by simp)
  rw [mixtureMeasure_apply _ (measurableSet_singleton _), hv]
  simp [Ne.symm hx2]

#print axioms solution

