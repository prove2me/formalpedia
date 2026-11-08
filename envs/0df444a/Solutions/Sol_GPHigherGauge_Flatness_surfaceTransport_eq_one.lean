-- Prove2me | solution 1 for GPHigherGauge.Flatness.surfaceTransport_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:29:01.661078+00:00
-- url     : https://prove2.me/submissions/86ba4f4f-7199-4e9e-a9f1-a6c4da495bbf

import Mathlib

theorem solution {G : Type*} [Group G] {H : Type*} (t : H → G) (g₁ g₂ : G) (h : H)
    (hsurf : t h = g₂ * g₁⁻¹) : g₂⁻¹ * t h * g₁ = 1 := by
  rw [hsurf]
  group
