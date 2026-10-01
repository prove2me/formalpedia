-- Prove2me | solution 1 for GFactorPhysics.nuclearMagneticMoment_eq
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:41.575974+00:00
-- url     : https://prove2.me/submissions/1285c902-dea1-47f1-9e48-ba6c452191f5

import Definitions.Def_GFactorPhysics_Defs

set_option autoImplicit false

open GFactorPhysics

theorem solution (g e hbar m_p : ℝ) (I : Fin 3 → ℝ) (hhbar : hbar ≠ 0) :
    nuclearMagneticMoment g (nuclearMagneton e hbar m_p) hbar I = (g * e / (2 * m_p)) • I := by
  unfold nuclearMagneticMoment nuclearMagneton
  by_cases massa_nula : m_p = 0
  · simp [massa_nula]
  congr 1
  field_simp [hhbar, massa_nula]
