-- Prove2me | solution 1 for FamousTheorems.additive_principal_ordinals_omega_powers_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:55:56.704184+00:00
-- url     : https://prove2.me/submissions/2d2f49da-fdfc-496d-8761-037760057b8b

import Mathlib

universe u

theorem solution {o : Ordinal.{u}} :
    Ordinal.IsPrincipal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (fun x : Ordinal.{u} => Ordinal.omega0 ^ x) :=
  Ordinal.isPrincipal_add_iff_zero_or_omega0_opow
