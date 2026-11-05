-- Prove2me | solution 1 for BookProof.QedFockGapChain.diagOnePart_no_form_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:57:02.580253+00:00
-- url     : https://prove2.me/submissions/becde9be-1a22-4d67-8b27-bdf44fcdd145

-- Generated from ChapterQedFockGapChain.lean — solution of BookProof.QedFockGapChain.diagOnePart_no_form_gap
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Theorems.Thm_BookProof_QedFockGapChain_diagOnePart_quadForm_basis
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
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} {k : ℕ}
    (hk : w k < m) :
    ∃ x : finiteModeDomain b, (x : F) ≠ 0 ∧
      quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
        < m * ‖(x : F)‖ ^ 2 := by

  have hnorm : ‖((modeBasis b k : finiteModeDomain b) : F)‖ = 1 := by
    rw [modeBasis_coe]; exact b.orthonormal.1 k
  refine ⟨modeBasis b k, ?_, ?_⟩
  · intro hc
    rw [hc] at hnorm
    simp at hnorm
  · rw [diagOnePart_quadForm_basis, hnorm]
    simpa using hk
