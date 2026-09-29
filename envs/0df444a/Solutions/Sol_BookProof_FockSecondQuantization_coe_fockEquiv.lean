-- Prove2me | solution 1 for BookProof.FockSecondQuantization.coe_fockEquiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:26:15.826734+00:00
-- url     : https://prove2.me/submissions/bcafb745-b109-421c-a7c4-377f1f9efdaf

import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert
noncomputable section

theorem solution (u : FockAlg) : ((fockEquiv u : lpFiniteModes Conf) : Fock) = toLp u := by
  rfl
