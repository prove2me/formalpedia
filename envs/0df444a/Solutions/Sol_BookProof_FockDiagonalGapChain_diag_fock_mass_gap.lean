-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diag_fock_mass_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-31T01:17:53.332+00:00
-- url     : https://prove2.me/submissions/50ad761c-83f2-4508-b7ad-a2b1db281934

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diag_fock_mass_gap
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_symmetricOn
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_quadForm_ge
import Theorems.Thm_BookProof_FockDiagonalGapChain_diag_fock_gap
import Theorems.Thm_BookProof_FockSecondQuantization_secondQuantization_friedrichs
import Theorems.Thm_BookProof_FockSecondQuantization_toLp_zero
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
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
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (hw : ∀ k, m ≤ w k) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (opCol b (diagOnePart b w))) A) ∧
      dGamma (opCol b (diagOnePart b w)) vac = 0 ∧
      (∀ u : FockAlg, u 0 = 0 →
        m * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re) ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re := by

  obtain ⟨hvac, hgap⟩ := diag_fock_gap b w hm.le hw
  refine ⟨?_, hvac, hgap, fun u h0 hu => ?_⟩
  · refine secondQuantization_friedrichs b (diagOnePart b w) (diagOnePart_symmetricOn b w)
      fun x => ?_
    have h := diagOnePart_quadForm_ge b w hw x
    have hx : (0 : ℝ) ≤ ‖(x : F)‖ ^ 2 := sq_nonneg _
    nlinarith
  · have hnorm : 0 < ‖toLp u‖ := by
      -- `by simpa using hc` simplified the goal to `toLp u = toLp 0` while
      -- `hc : toLp u = 0`, so the `exact`-step inside it never type-checked
      -- (platform CE, 2026-10-31).  Bridge with `toLp_zero`, as the sibling
      -- `YangMillsFockGapChain` solution already does.
      have : toLp u ≠ 0 := fun hc => hu (toLp_injective (hc.trans toLp_zero.symm))
      exact norm_pos_iff.mpr this
    have hquad := hgap u h0
    have hpos : 0 < m * ‖toLp u‖ ^ 2 := by positivity
    linarith
