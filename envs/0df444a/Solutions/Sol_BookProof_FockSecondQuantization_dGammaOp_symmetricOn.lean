-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGammaOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:39:21.3803+00:00
-- url     : https://prove2.me/submissions/7f189346-9744-4717-8b45-49b16deae360

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.dGammaOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_symm
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp col) := by

  intro x y
  rw [coe_dGammaOp, coe_dGammaOp, coe_fockEquiv_symm x, coe_fockEquiv_symm y]
  exact inner_dGamma_symm hherm _ _
