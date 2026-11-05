-- Prove2me | solution 1 for BookProof.QedFockGapChain.irPhoton_fock_mass_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:06.095594+00:00
-- url     : https://prove2.me/submissions/896a84fa-ab7c-4476-afb9-4991d2e2c4f2

-- Generated from ChapterQedFockGapChain.lean — solution of BookProof.QedFockGapChain.irPhoton_fock_mass_gap
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Theorems.Thm_BookProof_QedFockGapChain_irPhotonDispersion_ge
import Theorems.Thm_BookProof_FockDiagonalGapChain_diag_fock_mass_gap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.QedFockGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.FockDiagonalGapChain BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteCore
open BookProof.YangMillsFriedrichs


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {mu : ℝ} (hmu : 0 < mu) (p : ℕ → ℝ) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension
          (dGammaOp (opCol hermiteBasis
            (diagOnePart hermiteBasis (irPhotonDispersion mu p)))) A) ∧
      dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (irPhotonDispersion mu p))) vac
          = 0 ∧
      (∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma
              (opCol hermiteBasis
                (diagOnePart hermiteBasis (irPhotonDispersion mu p))) u)) : ℂ).re) ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma
            (opCol hermiteBasis
              (diagOnePart hermiteBasis (irPhotonDispersion mu p))) u)) : ℂ).re := diag_fock_mass_gap hermiteBasis (irPhotonDispersion mu p) hmu (irPhotonDispersion_ge mu p)
