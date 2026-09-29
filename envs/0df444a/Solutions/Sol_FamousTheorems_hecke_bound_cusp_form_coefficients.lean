-- Prove2me | solution 1 for FamousTheorems.hecke_bound_cusp_form_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:18:51.80201+00:00
-- url     : https://prove2.me/submissions/4e5794bd-ec09-4ede-9e28-1816abfa360b

import Mathlib

theorem solution {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F Γ k] (f : F) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion Γ.strictWidthInfty ⇑f))
      (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2)) :=
  CuspFormClass.qExpansion_isBigO f
