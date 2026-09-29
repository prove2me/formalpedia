-- Prove2me | solution 1 for FamousTheorems.cartan_dieudonne
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:29:12.59319+00:00
-- url     : https://prove2.me/submissions/aca9d39e-214d-4d74-9520-078776098bda

import Mathlib

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
    ∃ l : List F, l.length ≤ Module.finrank ℝ F ∧
      φ = (l.map fun v => Submodule.reflection (Submodule.span ℝ {v})ᗮ).prod :=
  φ.reflections_generate_dim
