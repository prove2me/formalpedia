-- Prove2me | solution 1 for DynamicsRelativity.kepler_orbit_conic_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T23:54:44.361702+00:00
-- url     : https://prove2.me/submissions/1f4bc816-9858-4cb0-a27e-de78bb41d3b9

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_kepler_runge_lenz_in_plane
import Theorems.Thm_DynamicsRelativity_kepler_eccentricity_lt_one
import Mathlib

open DynamicsRelativity

theorem solution {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hE : keplerEnergy k m x 0 < 0) :
    ∃ A : Vec, inner ℝ (angularMomentum m x 0) A = 0 ∧
      (∀ t, ‖x t‖ + inner ℝ A (x t) = (‖angularMomentum m x 0‖ / m) ^ 2 / k) ∧
      ‖A‖ < 1 := by
  obtain ⟨A, hAn, h_orbit⟩ := kepler_runge_lenz_in_plane hk h hL
  have hA_lt_one : ‖A‖ < 1 := kepler_eccentricity_lt_one hk h hL hE hAn h_orbit
  exact ⟨A, hAn, h_orbit, hA_lt_one⟩
