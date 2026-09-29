-- Prove2me | solution 1 for DynamicsRelativity.motion_in_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T00:06:49.464563+00:00
-- url     : https://prove2.me/submissions/adb9f839-b47e-4cde-ac94-34431bb35f84

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_angularMomentum_const
import Theorems.Thm_DynamicsRelativity_angularMomentum_orthogonal
import Mathlib

open DynamicsRelativity

theorem solution {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t : ℝ) :
    inner ℝ (angularMomentum m x 0) (x t) = 0 ∧
      inner ℝ (angularMomentum m x 0) (vel x t) = 0 := by
  have hL : angularMomentum m x 0 = angularMomentum m x t :=
    angularMomentum_const h 0 t
  rw [hL]
  exact angularMomentum_orthogonal m x t
