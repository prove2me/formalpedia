-- Prove2me | solution 1 for Diaz.quadratic_algebra_distance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:26:02.121531+00:00
-- url     : https://prove2.me/submissions/b742c757-957c-4de4-ac63-5d29b6583c22

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {R : Type*} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (A : Subring R)
    (hquad : ∀ z p q : R, p ∈ A → q ∈ A → z * z - p * z + q = 0 → z ∈ A)
    {u v : R} (hu : u * σ u ∈ A) (hv : v * σ v ∈ A)
    (huv : (u - v) * σ (u - v) ∈ A) :
    u * σ v ∈ A := by
  have htr : (u * σ v) + σ (u * σ v)
      = u * σ u + v * σ v - (u - v) * σ (u - v) := by
    simp only [map_mul, hσ, map_sub]; ring
  have hnz : (u * σ v) * σ (u * σ v) = (u * σ u) * (v * σ v) := by
    simp only [map_mul, hσ]; ring
  refine hquad (u * σ v) ((u * σ v) + σ (u * σ v)) ((u * σ v) * σ (u * σ v)) ?_ ?_ (by ring)
  · rw [htr]; exact A.sub_mem (A.add_mem hu hv) huv
  · rw [hnz]; exact A.mul_mem hu hv
