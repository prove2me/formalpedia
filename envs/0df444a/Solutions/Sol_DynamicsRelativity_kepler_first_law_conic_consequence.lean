-- Prove2me | solution 1 for DynamicsRelativity.kepler_first_law_conic_consequence
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T23:47:32.342263+00:00
-- url     : https://prove2.me/submissions/478cd7b5-8b5d-4194-98c5-bcd247a8f9e6

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_conic_ecc_lt_one_isEllipse
import Theorems.Thm_DynamicsRelativity_motion_in_plane
import Theorems.Thm_DynamicsRelativity_kepler_orbit_conic_plane
import Mathlib

open DynamicsRelativity

theorem solution {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hE : keplerEnergy k m x 0 < 0) :
    ∃ S : Set Vec, IsEllipseWithFocusAtOrigin S ∧ ∀ t, x t ∈ S := by
  obtain ⟨A, hAn, h_orbit, hA_lt_one⟩ := kepler_orbit_conic_plane hk h hL hE
  let n := angularMomentum m x 0
  let r₀ := (‖n‖ / m) ^ 2 / k
  have hr₀ : 0 < r₀ := by
    have h_norm_pos : 0 < ‖n‖ := norm_pos_iff.mpr hL
    have hm_pos : 0 < m := h.mass_pos
    first
    | positivity
    | exact div_pos (pow_pos (div_pos h_norm_pos hm_pos) 2) hk
  have h_ellipse : IsEllipseWithFocusAtOrigin {y : Vec | inner ℝ n y = 0 ∧ ‖y‖ + inner ℝ A y = r₀} :=
    conic_ecc_lt_one_isEllipse hL hAn hr₀ hA_lt_one
  refine ⟨{y : Vec | inner ℝ n y = 0 ∧ ‖y‖ + inner ℝ A y = r₀}, h_ellipse, fun t => ?_⟩
  exact ⟨(motion_in_plane h t).1, h_orbit t⟩
