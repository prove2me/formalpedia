-- Prove2me | solution 1 for BookProof.FockSecondQuantization.ymFockCol_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:06:04.595462+00:00
-- url     : https://prove2.me/submissions/22617d09-04d7-4652-bb48-220e934c8c37

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.ymFockCol_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_opCol_apply
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology
















open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (k j : ℕ) :
    ymFockCol e fabc k j
      = inner ℂ (coreBasis e j)
          (ymHamiltonian (coreRepBasis e) fabc
            ⟨coreBasis e k, Submodule.subset_span ⟨k, rfl⟩⟩) := opCol_apply _ _ k j
