-- Prove2me | solution 1 for BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:21.146564+00:00
-- url     : https://prove2.me/submissions/bb47f641-db59-463b-996e-53c77ff5eadb

-- Generated from ChapterDiffuseUnitaryModel.lean — solution of BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_cdfUnitary_apply
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_memLp_top_comp_cdf
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
theorem solution {g : ℝ → ℂ}
    (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    cdfUnitary mu (multOp g hg u) =
      multOp (fun x => g (cdf mu x)) (memLp_top_comp_cdf mu hg) (cdfUnitary mu u) := by

  refine Lp.ext ?_
  have h1 := cdfComp_coeFn mu (multOp g hg u)
  have h2 := (measurePreserving_cdf mu).quasiMeasurePreserving.ae_eq_comp
    (multOp_coeFn (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) g hg u)
  have h3 := multOp_coeFn (μ := mu) (fun x => g (cdf mu x)) (memLp_top_comp_cdf mu hg)
    (cdfComp mu u)
  have h4 := cdfComp_coeFn mu u
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply] at hx2
  rw [cdfUnitary_apply, cdfUnitary_apply, hx1, hx2, hx3, hx4]
