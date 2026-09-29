-- Prove2me | solution 1 for DynamicsRelativity.kepler_runge_lenz_in_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T00:01:58.102977+00:00
-- url     : https://prove2.me/submissions/8a51a7ad-3396-4dbb-a2e0-749c735493ea

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_kepler_orbit_conic
import Theorems.Thm_DynamicsRelativity_motion_in_plane
import Theorems.Thm_DynamicsRelativity_vector_project_plane_orbit
import Mathlib

open DynamicsRelativity

theorem solution {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) :
    ∃ A : Vec, inner ℝ (angularMomentum m x 0) A = 0 ∧
      ∀ t, ‖x t‖ + inner ℝ A (x t) = (‖angularMomentum m x 0‖ / m) ^ 2 / k := by
  obtain ⟨A, h_orbit⟩ := kepler_orbit_conic hk h hL
  have h_plane : ∀ t, inner ℝ (angularMomentum m x 0) (x t) = 0 := fun t => (motion_in_plane h t).1
  exact vector_project_plane_orbit hL h_plane h_orbit
