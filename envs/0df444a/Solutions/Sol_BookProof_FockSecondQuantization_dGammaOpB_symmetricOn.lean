-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGammaOpB_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:39:22.964478+00:00
-- url     : https://prove2.me/submissions/6f48328f-993b-4c2d-ad52-6e2bce23403d

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.dGammaOpB_symmetricOn
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_symmetricOn
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (fockBasisN ε)) (dGammaOpB ε col) := by

  intro x y
  exact dGammaOp_symmetricOn hherm
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) y)
