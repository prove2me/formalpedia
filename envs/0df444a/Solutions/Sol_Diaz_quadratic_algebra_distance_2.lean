-- Prove2me | solution 2 for Diaz.quadratic_algebra_distance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:18:32.850538+00:00
-- url     : https://prove2.me/submissions/b09a6717-1525-4740-9656-e353f12db22b

/-
`Diaz.quadratic_algebra_distance` is `Diaz.trace_norm_quadratic_algebra` fed to
the integrality hypothesis: the two identities of that node say that the trace
and the norm of `u σv` are polynomial in the three given norms, so both lie in
`A`, and `u σv` is a root of `X² - (trace) X + (norm)`.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_trace_norm_quadratic_algebra

open ComplexConjugate
open Diaz

theorem solution {R : Type*} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (A : Subring R)
    (hquad : ∀ z p q : R, p ∈ A → q ∈ A → z * z - p * z + q = 0 → z ∈ A)
    {u v : R} (hu : u * σ u ∈ A) (hv : v * σ v ∈ A)
    (huv : (u - v) * σ (u - v) ∈ A) :
    u * σ v ∈ A := by
  obtain ⟨htr, hnz⟩ := Diaz.trace_norm_quadratic_algebra σ hσ u v
  refine hquad (u * σ v) ((u * σ v) + σ (u * σ v)) ((u * σ v) * σ (u * σ v)) ?_ ?_ (by ring)
  · rw [htr]; exact A.sub_mem (A.add_mem hu hv) huv
  · rw [hnz]; exact A.mul_mem hu hv
