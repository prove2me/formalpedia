-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGamma_single
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:35:15.468077+00:00
-- url     : https://prove2.me/submissions/a5b87ef5-221a-4282-945d-63d089ec6d5b

import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem solution (col : ℕ → (ℕ →₀ ℂ)) (β : Conf) (c : ℂ) :
    dGamma col (Finsupp.single β c)
      = c • ∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)) := by
  simp [dGamma]
