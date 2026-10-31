-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:48.756364+00:00
-- url     : https://prove2.me/submissions/814dd058-8921-4f0f-864b-8e1881547fbe

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_diag_isPosCol_shiftCol
import Theorems.Thm_BookProof_FockFieldPerturbation_fock_gap_of_field_perturbation_pos
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockDiagonalGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore BookProof.ScalaronFockGapChain
open Module
open BookProof.FockSecondQuantization


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hm : 0 < m) (hw : ∀ k, m ≤ w k) {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < m)
    {u : FockAlg} (h0 : u 0 = 0) :
    0 < m - 2 * l2norm f ∧
      (m - 2 * l2norm f) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re := fock_gap_of_field_perturbation_pos hm (diag_isPosCol_shiftCol b w hw) hf h0
