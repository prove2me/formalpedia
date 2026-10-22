-- Prove2me | solution 1 for BirkhoffGlobalSection.star_shaped_level_set_convex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T18:28:48.209813+00:00
-- url     : https://prove2.me/submissions/6719cd55-d260-4c38-b209-63ec21809c52

import Theorems.Thm_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex
import Theorems.Thm_BirkhoffGlobalSection_radial_filling_locally_convex_of_positive_tangential_hessian

open BirkhoffGlobalSection

theorem solution (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    Convex ℝ {y : Phase | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s} := by
  have hlocal :=
    radial_filling_locally_convex_of_positive_tangential_hessian
      F S hS hF0 hreg hTH hray huniq hneg
  exact closed_preconnected_locally_convex_is_convex _ hlocal.1 hlocal.2.1 hlocal.2.2
