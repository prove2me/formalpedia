-- Prove2me | solution 1 for BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:40:55.092944+00:00
-- url     : https://prove2.me/submissions/d3819088-cece-4369-8461-101c2e55058c

-- Generated from ChapterAbelianClassificationList.lean — solution of BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_cdfUnitary_intertwines
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_memLp_top_comp_cdf
import Theorems.Thm_BookProof_ChapterLpScaleMeasure_scaleUnitary_intertwines
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterAbelianClassificationList



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (nu : Measure ℝ) [IsFiniteMeasure nu] [NullSingletonClass nu]

set_option maxHeartbeats 1000000 in
theorem solution (hne : nu Set.univ ≠ 0) :
    ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 nu,
      ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (U (multOp g hg u) : ℝ → ℂ)
          =ᵐ[nu] fun x => g (cdf (normalized nu) x) * (U u : ℝ → ℂ) x := by

  haveI : IsProbabilityMeasure (normalized nu) := isProbabilityMeasure_normalized nu hne
  have hc0 : (nu Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top nu _)
  have hctop : (nu Set.univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
  refine ⟨(cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop), fun g hg u => ?_⟩
  have hstep := cdfUnitary_intertwines (normalized nu) hg u
  have hmul := scaleUnitary_intertwines (nu := nu) hc0 hctop
    (memLp_top_comp_cdf (normalized nu) hg) (cdfUnitary (normalized nu) u)
  calc ((((cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop)) (multOp g hg u) :
        Lp ℂ 2 nu) : ℝ → ℂ)
      = ((scaleUnitary hc0 hctop (multOp (fun x => g (cdf (normalized nu) x))
          (memLp_top_comp_cdf (normalized nu) hg)
            (cdfUnitary (normalized nu) u)) : Lp ℂ 2 nu) : ℝ → ℂ) := by
        have htrans : ∀ w : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
            ((cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop) w : Lp ℂ 2 nu)
              = (scaleUnitary hc0 hctop (cdfUnitary (normalized nu) w) : Lp ℂ 2 nu) :=
          fun _ => LinearIsometryEquiv.trans_apply _ _ _
        rw [htrans, hstep]
    _ =ᵐ[nu] fun x => g (cdf (normalized nu) x) *
          ((scaleUnitary hc0 hctop (cdfUnitary (normalized nu) u) : Lp ℂ 2 nu) : ℝ → ℂ) x :=
        hmul
    _ = fun x => g (cdf (normalized nu) x) *
          (((cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop) u :
            Lp ℂ 2 nu) : ℝ → ℂ) x := rfl
