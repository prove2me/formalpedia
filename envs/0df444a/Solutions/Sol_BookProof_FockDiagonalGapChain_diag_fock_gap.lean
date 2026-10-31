-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diag_fock_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:36.874458+00:00
-- url     : https://prove2.me/submissions/cf1ae8a4-cd56-483e-81f0-c8f2b0725640

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diag_fock_gap
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_quadForm_ge
import Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_one_particle_form_gap
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
import Definitions.Def_ChapterFockOneParticleGap
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
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hw : ∀ k, m ≤ w k) :
    dGamma (opCol b (diagOnePart b w)) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        m * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re := fock_gap_of_one_particle_form_gap b (diagOnePart b w) hm (diagOnePart_quadForm_ge b w hw)
