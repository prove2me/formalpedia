-- Prove2me | solution 1 for BookProof.QedFockGapChain.photon_fock_positivity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T22:57:56.946911+00:00
-- url     : https://prove2.me/submissions/d27217af-6ccc-42d4-a8f3-23eae64ab28f

-- Generated from ChapterQedFockGapChain.lean — solution of BookProof.QedFockGapChain.photon_fock_positivity
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Theorems.Thm_BookProof_QedFockGapChain_photonDispersion_nonneg
import Theorems.Thm_BookProof_FockDiagonalGapChain_diag_fock_gap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
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


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) :
    dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (0 : ℝ) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma
              (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) u)) : ℂ).re := diag_fock_gap hermiteBasis (photonDispersion p) le_rfl (fun k => photonDispersion_nonneg p k)
