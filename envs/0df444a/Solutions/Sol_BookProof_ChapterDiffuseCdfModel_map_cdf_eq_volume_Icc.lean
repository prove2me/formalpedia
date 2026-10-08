-- Prove2me | solution 1 for BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T15:37:12.253604+00:00
-- url     : https://prove2.me/submissions/8d4e8462-a721-46b8-9d6d-dc90265736d0

-- Generated from ChapterDiffuseCdfModel.lean — solution of BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
import Theorems.Thm_BookProof_ChapterDiffuseCdfModel_measure_cdf_le
import Theorems.Thm_BookProof_ChapterDiffuseCdfModel_volume_Icc_inter_Iic
open BookProof.ChapterDiffuseCdfModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

variable (mu : Measure ℝ)

set_option maxHeartbeats 1000000 in
theorem solution [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Measure.map (cdf mu) mu = volume.restrict (Set.Icc (0 : ℝ) 1) := by

  have hmeas : Measurable (cdf mu) := (cdf mu).mono.measurable
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply hmeas measurableSet_Iic]
  have hpre : (cdf mu) ⁻¹' Set.Iic t = {x : ℝ | cdf mu x ≤ t} := rfl
  rw [hpre]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hempty : {x : ℝ | cdf mu x ≤ t} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht (cdf_nonneg mu x)
    have hempty' : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
      obtain ⟨hy1, hy0, -⟩ := hy
      exact absurd (le_trans hy0 hy1) (by linarith)
    rw [hempty, Measure.restrict_apply measurableSet_Iic, hempty']
    simp
  · subst ht
    rw [measure_cdf_le mu le_rfl one_pos, volume_Icc_inter_Iic zero_le_one]
  · rcases lt_or_ge t 1 with ht1 | ht1
    · rw [measure_cdf_le mu ht.le ht1, volume_Icc_inter_Iic ht1.le]
    · have huniv : {x : ℝ | cdf mu x ≤ t} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans (cdf_le_one mu x) ht1
      have hIcc : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨-, hy⟩
          exact hy
        · rintro ⟨hy0, hy1⟩
          exact ⟨le_trans hy1 ht1, hy0, hy1⟩
      rw [huniv, Measure.restrict_apply measurableSet_Iic, hIcc, Real.volume_Icc,
        measure_univ]
      simp
