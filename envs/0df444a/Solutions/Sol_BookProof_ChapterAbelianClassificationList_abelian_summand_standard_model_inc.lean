-- Prove2me | solution 1 for BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:42:04.060969+00:00
-- url     : https://prove2.me/submissions/198165f6-7ac7-4c65-b70d-f33b14250cdf

-- Generated from ChapterAbelianClassificationList.lean — solution of BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Theorems.Thm_BookProof_ChapterAtomicDiagonalModel_atomic_multiplication_model_diagonal
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_isHilbertSum_splitEmbed
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_intertwines
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_measurableSet_atomSet
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLpScaleMeasure
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterAbelianClassificationList



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (nu : Measure ℝ) [IsFiniteMeasure nu] [NullSingletonClass nu]
variable (mu : Measure ℝ) [IsProbabilityMeasure mu]

set_option maxHeartbeats 1000000 in
theorem solution :
    (IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b)))
        (splitEmbed (measurableSet_atomSet mu))) ∧
      (∀ (b : Bool) (g : ℝ → ℂ) (hg : MemLp g ⊤ mu)
          (u : Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b))),
        splitEmbed (measurableSet_atomSet mu) b (multOp g (hg.restrict _) u)
          = multOp g hg (splitEmbed (measurableSet_atomSet mu) b u)) ∧
      (∃ B : HilbertBasis (atomSet (mu.restrict (atomSet mu))) ℂ
          (Lp ℂ 2 (mu.restrict (atomSet mu))),
        ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (mu.restrict (atomSet mu)))
          (a : atomSet (mu.restrict (atomSet mu))),
          multOp g hg (B a) = g (a : ℝ) • B a) ∧
      (mu (atomSet mu)ᶜ ≠ 0 →
        ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ]
            Lp ℂ 2 (mu.restrict (atomSet mu)ᶜ),
          ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
            (U (multOp g hg u) : ℝ → ℂ)
              =ᵐ[mu.restrict (atomSet mu)ᶜ] fun x =>
                g (cdf (normalized (mu.restrict (atomSet mu)ᶜ)) x) * (U u : ℝ → ℂ) x) := by

  refine ⟨isHilbertSum_splitEmbed (measurableSet_atomSet mu), ?_,
    atomic_multiplication_model_diagonal _ (restrict_atomSet_pure mu), ?_⟩
  · intro b g hg u
    exact restrictEmbed_intertwines (measurableSet_splitSet (measurableSet_atomSet mu) b) hg u
  · intro hne
    have hmass : (mu.restrict (atomSet mu)ᶜ) Set.univ ≠ 0 := by
      rwa [Measure.restrict_apply_univ]
    exact diffuse_finite_multiplication_model _ hmass
