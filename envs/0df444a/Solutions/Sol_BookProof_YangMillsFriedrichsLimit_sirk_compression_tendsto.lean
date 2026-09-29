-- Prove2me | solution 1 for BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:20.756793+00:00
-- url     : https://prove2.me/submissions/49fa62f5-0401-4be9-a270-2581c68c8ff0

-- Generated from ChapterYangMillsFriedrichsLimit.lean — solution of BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Theorems.Thm_BookProof_YangMillsFriedrichsLimit_krylov_starProjection_tendsto
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterFarisLavine
open BookProof.YangMillsFriedrichsLimit









open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F)) (u : F) :
    Filter.Tendsto (fun n : ℕ => sirkCompression A v n u) Filter.atTop (nhds (A u)) := by

  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- `‖Pₙ A Pₙ u − A u‖ ≤ ‖A‖ ‖Pₙ u − u‖ + ‖Pₙ (A u) − A u‖`
  have hbound : ∀ n : ℕ, ‖sirkCompression A v n u - A u‖
      ≤ ‖A‖ * ‖(krylovSpan A.toLinearMap v n).starProjection u - u‖
        + ‖(krylovSpan A.toLinearMap v n).starProjection (A u) - A u‖ := by
    intro n
    have hsplit : sirkCompression A v n u - A u
        = (krylovSpan A.toLinearMap v n).starProjection
            (A ((krylovSpan A.toLinearMap v n).starProjection u) - A u)
          + ((krylovSpan A.toLinearMap v n).starProjection (A u) - A u) := by
      simp only [sirkCompression, map_sub]
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans ((krylovSpan A.toLinearMap v n).norm_starProjection_apply_le _) ?_
    have hAsub : A ((krylovSpan A.toLinearMap v n).starProjection u) - A u
        = A ((krylovSpan A.toLinearMap v n).starProjection u - u) := by rw [map_sub]
    rw [hAsub]
    exact A.le_opNorm _
  have h1 : Filter.Tendsto
      (fun n : ℕ => ‖A‖ * ‖(krylovSpan A.toLinearMap v n).starProjection u - u‖)
      Filter.atTop (nhds 0) := by
    have := krylov_starProjection_tendsto A v hdense u
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this.const_mul ‖A‖
  have h2 : Filter.Tendsto
      (fun n : ℕ => ‖(krylovSpan A.toLinearMap v n).starProjection (A u) - A u‖)
      Filter.atTop (nhds 0) := by
    have := krylov_starProjection_tendsto A v hdense (A u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this
  have hsum : Filter.Tendsto
      (fun n : ℕ => ‖A‖ * ‖(krylovSpan A.toLinearMap v n).starProjection u - u‖
        + ‖(krylovSpan A.toLinearMap v n).starProjection (A u) - A u‖)
      Filter.atTop (nhds 0) := by simpa using h1.add h2
  refine squeeze_zero (fun n => norm_nonneg _) hbound hsum
