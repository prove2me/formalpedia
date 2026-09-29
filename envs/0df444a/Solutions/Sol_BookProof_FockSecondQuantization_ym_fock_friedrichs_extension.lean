-- Prove2me | solution 1 for BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:42:17.268237+00:00
-- url     : https://prove2.me/submissions/05ea5bbe-9576-4d39-9190-076268d1e521

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_secondQuantization_friedrichs
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm_nonneg
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
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
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A :=
  secondQuantization_friedrichs (coreBasis e) (ymOnePart e fabc)
      (ymHamiltonian_symmetricOn (coreRepBasis e) fabc)
      (ymHamiltonian_quadForm_nonneg (coreRepBasis e) fabc)
