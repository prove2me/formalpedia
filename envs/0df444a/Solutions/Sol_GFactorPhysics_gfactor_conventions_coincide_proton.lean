-- Prove2me | solution 1 for GFactorPhysics.gfactor_conventions_coincide_proton
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:36.283519+00:00
-- url     : https://prove2.me/submissions/9246a7c5-a2d4-4589-888f-7b9f54113342

import Definitions.Def_GFactorPhysics_Defs

set_option autoImplicit false

open GFactorPhysics

theorem solution (g₁ g₂ e hbar m_p : ℝ) (S : Fin 3 → ℝ)
    (he : 0 < e) (hhbar : 0 < hbar) (hm_p : 0 < m_p) (hS : S ≠ 0)
    (h : diracMagneticMoment g₁ e m_p S =
      nuclearMagneticMoment g₂ (nuclearMagneton e hbar m_p) hbar S) :
    g₁ = g₂ := by
  unfold diracMagneticMoment nuclearMagneticMoment nuclearMagneton at h
  have coeficiente := smul_left_injective ℝ hS h
  have cancelar_hbar :
      g₂ * (e * hbar / (2 * m_p)) / hbar = g₂ * e / (2 * m_p) := by
    field_simp [ne_of_gt hhbar, ne_of_gt hm_p]
  rw [cancelar_hbar] at coeficiente
  have numeradores := (div_left_inj' (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt hm_p))).mp coeficiente
  exact mul_right_cancel₀ (ne_of_gt he) numeradores
