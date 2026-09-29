-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:39:20.573567+00:00
-- url     : https://prove2.me/submissions/6a4d36f3-4428-4dc3-8856-573fd39e2f21

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_nonneg
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes Conf) : 0 ≤ quadForm (dGammaOp col) x := by

  rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
  exact inner_dGamma_nonneg hpos _
