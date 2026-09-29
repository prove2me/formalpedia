-- Prove2me | solution 1 for BookProof.FockSecondQuantization.modes_right_subset_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:35:21.188633+00:00
-- url     : https://prove2.me/submissions/29390aee-be0b-46b2-b770-a992c8ad2ba3

import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem solution (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes v ⊆ closureModes col u v := by
  intro k hk
  simp [closureModes, hk]
