-- Prove2me | solution 1 for GFactorPhysics.orbital_moment_z_component
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:43.09899+00:00
-- url     : https://prove2.me/submissions/03a06804-933f-4efb-a693-10d76c6bd0c3

import Definitions.Def_GFactorPhysics_Defs

set_option autoImplicit false

open GFactorPhysics

theorem solution (g_L μB hbar m_l : ℝ) (L : Fin 3 → ℝ)
    (hhbar : hbar ≠ 0) (hLz : L 2 = m_l * hbar) :
    electronOrbitalMagneticMoment g_L μB hbar L 2 = -g_L * μB * m_l ∧
      (g_L = 1 → electronOrbitalMagneticMoment g_L μB hbar L 2 = -μB * m_l) := by
  have componente : electronOrbitalMagneticMoment g_L μB hbar L 2 = -g_L * μB * m_l := by
    simp only [electronOrbitalMagneticMoment, Pi.smul_apply, smul_eq_mul, hLz]
    field_simp [hhbar]
  refine ⟨componente, ?_⟩
  intro fator
  simpa [fator] using componente
