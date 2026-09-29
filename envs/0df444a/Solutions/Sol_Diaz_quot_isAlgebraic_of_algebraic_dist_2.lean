-- Prove2me | solution 2 for Diaz.quot_isAlgebraic_of_algebraic_dist
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:18:33.616863+00:00
-- url     : https://prove2.me/submissions/4a23d1f8-e15d-4bdd-a122-b45bfcfc24c7

/-
`Diaz.quot_isAlgebraic_of_algebraic_dist` through
`Diaz.trace_norm_quadratic_algebra` at `σ = ` complex conjugation: that node's
two identities are exactly the statements that the trace and the norm of
`u v̄` are polynomial in `u ū`, `v v̄` and `(u-v)(ū-v̄)`.  Dividing by `v v̄`
turns them into the coefficients of a quadratic over `K` satisfied by `u/v`.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_trace_norm_quadratic_algebra

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {K : Subfield ℂ} {u v : ℂ} (hv0 : v ≠ 0)
    (hu : u * conj u ∈ K) (hv : v * conj v ∈ K)
    (hd : (u - v) * conj (u - v) ∈ K) :
    IsAlgebraic (↥K) (u / v) := by
  have hcv : conj v ≠ 0 := by simpa using hv0
  have hc0 : v * conj v ≠ 0 := mul_ne_zero hv0 hcv
  obtain ⟨htr, hnz⟩ :=
    Diaz.trace_norm_quadratic_algebra (starRingEnd ℂ) (fun x => Complex.conj_conj x) u v
  have hcm : conj (u * conj v) = conj u * v := by rw [map_mul, Complex.conj_conj]
  have hs : u * conj v + conj u * v ∈ K := by
    have e : u * conj v + conj u * v = (u * conj v) + conj (u * conj v) := by rw [hcm]
    rw [e, htr]; exact K.sub_mem (K.add_mem hu hv) hd
  have hp : (u * conj v) * (conj u * v) ∈ K := by
    have e : (u * conj v) * (conj u * v) = (u * conj v) * conj (u * conj v) := by rw [hcm]
    rw [e, hnz]; exact K.mul_mem hu hv
  refine ⟨Polynomial.X ^ 2
      - Polynomial.C (⟨(u * conj v + conj u * v) / (v * conj v), K.div_mem hs hv⟩ : ↥K)
        * Polynomial.X
      + Polynomial.C (⟨((u * conj v) * (conj u * v)) / ((v * conj v) * (v * conj v)),
          K.div_mem hp (K.mul_mem hv hv)⟩ : ↥K), ?_, ?_⟩
  · intro hzero
    have h2 := congrArg (fun p => Polynomial.coeff p 2) hzero
    simp at h2
  · simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    show (u / v) ^ 2 - ((u * conj v + conj u * v) / (v * conj v)) * (u / v)
      + ((u * conj v) * (conj u * v)) / ((v * conj v) * (v * conj v)) = 0
    field_simp
    ring
