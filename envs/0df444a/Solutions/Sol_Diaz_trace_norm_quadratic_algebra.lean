-- Prove2me | solution 1 for Diaz.trace_norm_quadratic_algebra
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:34.582422+00:00
-- url     : https://prove2.me/submissions/5a95accc-6c57-4d58-86c0-a63fc40998f8

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {R : Type*} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (u v : R) :
    (u * σ v) + σ (u * σ v)
        = u * σ u + v * σ v - (u - v) * σ (u - v)
      ∧ (u * σ v) * σ (u * σ v) = (u * σ u) * (v * σ v) := by
  constructor
  · simp only [map_mul, hσ, map_sub]
    ring
  · simp only [map_mul, hσ]
    ring
