-- Prove2me | solution 1 for BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:58:37.524982+00:00
-- url     : https://prove2.me/submissions/059ea448-58ea-4b46-ae88-744dc27d2703

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc
import Mathlib
import Definitions.Def_ChapterAbelianMixture
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal

namespace BookProof.ChapterAbelianMixture
theorem mixtureMeasure_diffuse_mass : mixtureMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
  rw [mixtureMeasure_apply _ measurableSet_Icc]
  have h2 : ((2 : ℝ)) ∉ Set.Icc (0 : ℝ) 1 := by norm_num
  simp [Real.volume_Icc, Measure.dirac_apply' _ measurableSet_Icc, h2]

theorem mixtureMeasure_diffuse_point {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    mixtureMeasure {x} = 0 := by
  have hx2 : x ≠ 2 := by
    rcases hx with ⟨_, hx1⟩
    intro h; rw [h] at hx1; norm_num at hx1
  have hv : MeasureTheory.volume ({x} ∩ Set.Icc (0 : ℝ) 1) = 0 :=
    measure_mono_null Set.inter_subset_left (by simp)
  rw [mixtureMeasure_apply _ (measurableSet_singleton _), hv]
  simp [Ne.symm hx2]
end BookProof.ChapterAbelianMixture

theorem solution :
    0 < mixtureMeasure (Set.Icc (0 : ℝ) 1) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, mixtureMeasure {x} = 0 := by
  refine ⟨?_, fun x hx => mixtureMeasure_diffuse_point hx⟩
  rw [mixtureMeasure_diffuse_mass]
  exact zero_lt_one

#print axioms solution

