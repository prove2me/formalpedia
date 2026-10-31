-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diagOnePart_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:29.008368+00:00
-- url     : https://prove2.me/submissions/fcd4157a-5a51-4b0e-9340-d60ca980bd5d

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diagOnePart_symmetricOn
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_inner
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockDiagonalGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore BookProof.ScalaronFockGapChain
open Module
open BookProof.HermiteGalerkin


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) :
    SymmetricOn (finiteModeDomain b)
      ((finiteModeDomain b).subtype.comp (diagOnePart b w)) := by

  classical
  intro x y
  have hDx : ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
      = ((diagOnePart b w x : finiteModeDomain b) : F) := rfl
  have hDy : ((finiteModeDomain b).subtype.comp (diagOnePart b w)) y
      = ((diagOnePart b w y : finiteModeDomain b) : F) := rfl
  have hswap : (inner ℂ ((diagOnePart b w x : finiteModeDomain b) : F) (y : F) : ℂ)
      = (starRingEnd ℂ)
          (inner ℂ (y : F) ((diagOnePart b w x : finiteModeDomain b) : F) : ℂ) :=
    (inner_conj_symm (𝕜 := ℂ) ((diagOnePart b w x : finiteModeDomain b) : F) (y : F)).symm
  rw [hDx, hDy, hswap, diagOnePart_inner b w y x, diagOnePart_inner b w x y, map_sum]
  set lx := (modeBasis b).repr x with hlx
  set ly := (modeBasis b).repr y with hly
  have key : ∀ i : ℕ,
      (starRingEnd ℂ) (((w i : ℝ) : ℂ) * (starRingEnd ℂ) (ly i) * lx i)
        = ((w i : ℝ) : ℂ) * (starRingEnd ℂ) (lx i) * ly i := by
    intro i
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  calc ∑ i ∈ lx.support, (starRingEnd ℂ) (((w i : ℝ) : ℂ) * (starRingEnd ℂ) (ly i) * lx i)
      = ∑ i ∈ lx.support ∪ ly.support,
          (starRingEnd ℂ) (((w i : ℝ) : ℂ) * (starRingEnd ℂ) (ly i) * lx i) := by
        refine Finset.sum_subset
          (Finset.subset_union_left (s₁ := lx.support) (s₂ := ly.support)) ?_
        intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
    _ = ∑ i ∈ lx.support ∪ ly.support,
          ((w i : ℝ) : ℂ) * (starRingEnd ℂ) (lx i) * ly i :=
        Finset.sum_congr rfl fun i _ => key i
    _ = ∑ i ∈ ly.support, ((w i : ℝ) : ℂ) * (starRingEnd ℂ) (lx i) * ly i := by
        refine (Finset.sum_subset
          (Finset.subset_union_right (s₁ := lx.support) (s₂ := ly.support)) ?_).symm
        intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
