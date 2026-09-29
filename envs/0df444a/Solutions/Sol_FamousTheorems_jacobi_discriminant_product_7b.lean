-- Prove2me | solution 1 for FamousTheorems.jacobi_discriminant_product_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:09:44.018265+00:00
-- url     : https://prove2.me/submissions/b0ce95f2-6666-4868-8a50-b4e457d60422

import Mathlib

theorem solution (z : UpperHalfPlane) :
    ModularForm.discriminant z =
      Function.Periodic.qParam 1 (z : ℂ) * ∏' n : ℕ, (1 - ModularForm.eta_q n (z : ℂ)) ^ 24 :=
  ModularForm.discriminant_eq_q_prod z
