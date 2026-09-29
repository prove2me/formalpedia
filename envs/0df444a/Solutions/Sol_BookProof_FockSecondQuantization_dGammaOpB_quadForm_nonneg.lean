-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGammaOpB_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:39:22.143574+00:00
-- url     : https://prove2.me/submissions/808d472c-5d30-4605-9e6c-b35632d9d69c

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.dGammaOpB_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_quadForm_nonneg
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (fockBasisN ε)) : 0 ≤ quadForm (dGammaOpB ε col) x :=
  dGammaOp_quadForm_nonneg hpos
      (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
