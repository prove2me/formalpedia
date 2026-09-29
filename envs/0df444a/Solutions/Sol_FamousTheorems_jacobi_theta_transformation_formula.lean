-- Prove2me | solution 1 for FamousTheorems.jacobi_theta_transformation_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:17:28.230866+00:00
-- url     : https://prove2.me/submissions/3341ade2-3bc8-4132-88cc-18e877c6e870

import Mathlib

theorem solution (τ : UpperHalfPlane) :
    jacobiTheta ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ :=
  jacobiTheta_S_smul τ
