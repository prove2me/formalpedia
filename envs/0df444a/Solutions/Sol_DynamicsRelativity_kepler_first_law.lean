-- Prove2me | solution 1 for DynamicsRelativity.kepler_first_law
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T23:35:01.972037+00:00
-- url     : https://prove2.me/submissions/1114c5c3-998f-4cd7-b874-e4498353ac43

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_kepler_first_law_conic_consequence
import Mathlib

open DynamicsRelativity

theorem solution {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hE : keplerEnergy k m x 0 < 0) :
    ∃ S : Set Vec, IsEllipseWithFocusAtOrigin S ∧ ∀ t, x t ∈ S := by
  exact DynamicsRelativity.kepler_first_law_conic_consequence hk h hL hE
