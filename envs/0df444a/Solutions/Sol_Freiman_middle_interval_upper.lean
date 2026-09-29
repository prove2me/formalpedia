-- Prove2me | solution 1 for Freiman.middle_interval_upper
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T19:02:11.003242+00:00
-- url     : https://prove2.me/submissions/f27a77f0-e92c-4f02-9098-5251978f6331

import Theorems.Thm_Freiman_upper_ray
import Theorems.Thm_Freiman_constant_order

open Freiman

theorem solution :
    Set.Icc upperRayStart (128 / 25 : ℝ) ⊆ lagrangeSpectrum := by
  have h_ray : Set.Ici upperRayStart ⊆ lagrangeSpectrum := upper_ray
  intro x hx
  apply h_ray
  exact hx.1
