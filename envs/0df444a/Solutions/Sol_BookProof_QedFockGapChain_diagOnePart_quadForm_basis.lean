-- Prove2me | solution 1 for BookProof.QedFockGapChain.diagOnePart_quadForm_basis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:46:35.87427+00:00
-- url     : https://prove2.me/submissions/7c15014f-a8fd-4cd1-a721-6916e719379f

-- Generated from ChapterQedFockGapChain.lean — solution of BookProof.QedFockGapChain.diagOnePart_quadForm_basis
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_inner_self_ofReal
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.QedFockGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.FockDiagonalGapChain BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.HermiteGalerkin


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (k : ℕ) :
    quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) (modeBasis b k) = w k := by

  have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
  have hq : quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) (modeBasis b k)
      = (inner ℂ ((modeBasis b k : finiteModeDomain b) : F)
          ((diagOnePart b w (modeBasis b k) : finiteModeDomain b) : F) : ℂ).re := rfl
  rw [hq, diagOnePart_basis, Submodule.coe_smul, modeBasis_coe, inner_smul_right,
    inner_self_ofReal, hnorm]
  simp
