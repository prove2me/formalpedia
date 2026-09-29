-- Prove2me | solution 2 for Freiman.middle_interval
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T19:02:29.307719+00:00
-- url     : https://prove2.me/submissions/e1b7f555-2315-4932-937c-e0b2429714a5

import Theorems.Thm_Freiman_middle_interval_upper
import Theorems.Thm_Freiman_middle_interval_lower
import Theorems.Thm_Freiman_constant_order
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

open Freiman

theorem solution :
    Set.Icc (Real.sqrt 21) (128 / 25 : ℝ) ⊆ lagrangeSpectrum := by
  intro x hx
  have h_ord₁ : Real.sqrt 21 ≤ upperRayStart := constant_order.2.2.2.1.le
  have h_ord₂ : upperRayStart < (128 / 25 : ℝ) := constant_order.2.2.2.2
  rcases le_total x upperRayStart with hx_le | hx_ge
  · exact middle_interval_lower ⟨hx.1, hx_le⟩
  · exact middle_interval_upper ⟨hx_ge, hx.2⟩
