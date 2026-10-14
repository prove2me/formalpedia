-- Prove2me | solution 1 for BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:35.124805+00:00
-- url     : https://prove2.me/submissions/7a5fd8f7-0261-4d1e-8d1e-3e2fa2d28d70

-- Generated from ChapterDiffuseUnitaryModel.lean — solution of BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_memLp_top_comp_cdf
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_cdfUnitary_intertwines
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Definitions.Def_ChapterDiffuseCdfModel
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterDiffuseUnitaryModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
      ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (U (multOp g hg u) : ℝ → ℂ) =ᵐ[mu] fun x => g (cdf mu x) * (U u : ℝ → ℂ) x := by

  refine ⟨cdfUnitary mu, fun g hg u => ?_⟩
  rw [cdfUnitary_intertwines mu hg u]
  exact multOp_coeFn _ _ _
