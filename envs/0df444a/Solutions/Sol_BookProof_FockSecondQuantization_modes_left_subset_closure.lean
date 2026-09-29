-- Prove2me | solution 1 for BookProof.FockSecondQuantization.modes_left_subset_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:35:18.268522+00:00
-- url     : https://prove2.me/submissions/7d052bc6-422d-447d-bf2b-092ed08b48a8

import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem solution (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes u ⊆ closureModes col u v := by
  intro k hk
  simp [closureModes, hk]
