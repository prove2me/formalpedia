-- Prove2me | solution 1 for BookProof.ChapterDiffuseCdfModel.measure_cdf_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:13:05.637981+00:00
-- url     : https://prove2.me/submissions/639c8a67-c7fe-4e89-9e44-58002dc131a5

-- Generated from ChapterDiffuseCdfModel.lean — solution of BookProof.ChapterDiffuseCdfModel.measure_cdf_le
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
import Theorems.Thm_BookProof_ChapterDiffuseCdfModel_exists_cdf_eq
open BookProof.ChapterDiffuseCdfModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

variable (mu : Measure ℝ)

set_option maxHeartbeats 1000000 in
theorem solution [IsProbabilityMeasure mu] [NullSingletonClass mu] {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : mu {x | cdf mu x ≤ t} = ENNReal.ofReal t := by

  refine le_antisymm ?_ ?_
  · have key : ∀ s : ℝ, t < s → s < 1 → mu {x | cdf mu x ≤ t} ≤ ENNReal.ofReal s := by
      intro s hts hs1
      obtain ⟨y, hy⟩ := exists_cdf_eq mu (lt_of_le_of_lt ht0 hts) hs1
      have hsub : {x : ℝ | cdf mu x ≤ t} ⊆ Set.Iic y := by
        intro z hz
        by_contra hzy
        have hyz : y < z := lt_of_not_ge hzy
        have hmono := (cdf mu).mono hyz.le
        rw [hy] at hmono
        exact absurd (le_trans hmono hz) (by linarith)
      calc mu {x | cdf mu x ≤ t} ≤ mu (Set.Iic y) := measure_mono hsub
        _ = ENNReal.ofReal (cdf mu y) := (ofReal_cdf mu y).symm
        _ = ENNReal.ofReal s := by rw [hy]
    have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal s) (nhdsWithin t (Set.Ioi t))
        (nhds (ENNReal.ofReal t)) :=
      (ENNReal.continuous_ofReal.tendsto t).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht1] with s hs hs1
    exact key s hs hs1.2
  · rcases eq_or_lt_of_le ht0 with h | h
    · simp [← h]
    · obtain ⟨x, hx⟩ := exists_cdf_eq mu h ht1
      have hsub : Set.Iic x ⊆ {y : ℝ | cdf mu y ≤ t} := by
        intro z hz
        have hm := (cdf mu).mono hz
        rw [hx] at hm
        exact hm
      calc ENNReal.ofReal t = ENNReal.ofReal (cdf mu x) := by rw [hx]
        _ = mu (Set.Iic x) := ofReal_cdf mu x
        _ ≤ mu {y | cdf mu y ≤ t} := measure_mono hsub
