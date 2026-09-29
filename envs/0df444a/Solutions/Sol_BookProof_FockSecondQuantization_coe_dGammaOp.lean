-- Prove2me | solution 1 for BookProof.FockSecondQuantization.coe_dGammaOp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:26:19.141709+00:00
-- url     : https://prove2.me/submissions/0898e055-62b3-402f-b5ce-324a6f4a7ae3

import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert
noncomputable section

theorem solution (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp col x = toLp (dGamma col (fockEquiv.symm x)) := by
  rfl
