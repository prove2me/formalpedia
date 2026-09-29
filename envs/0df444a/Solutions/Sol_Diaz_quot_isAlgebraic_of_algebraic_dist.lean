-- Prove2me | solution 1 for Diaz.quot_isAlgebraic_of_algebraic_dist
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:48.292755+00:00
-- url     : https://prove2.me/submissions/0ac19860-9a7a-4daf-b3e4-018a60219073

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {K : Subfield ℂ} {u v : ℂ} (hv0 : v ≠ 0)
    (hu : u * conj u ∈ K) (hv : v * conj v ∈ K)
    (hd : (u - v) * conj (u - v) ∈ K) :
    IsAlgebraic (↥K) (u / v) := by
  have hcv : conj v ≠ 0 := by simpa using hv0
  have hc0 : v * conj v ≠ 0 := mul_ne_zero hv0 hcv
  have hs : u * conj v + conj u * v ∈ K := by
    have e : u * conj v + conj u * v
        = u * conj u + v * conj v - (u - v) * conj (u - v) := by
      simp [map_sub]; ring
    rw [e]; exact K.sub_mem (K.add_mem hu hv) hd
  have hp : (u * conj v) * (conj u * v) ∈ K := by
    have e : (u * conj v) * (conj u * v) = (u * conj u) * (v * conj v) := by ring
    rw [e]; exact K.mul_mem hu hv
  refine ⟨Polynomial.X ^ 2
      - Polynomial.C (⟨(u * conj v + conj u * v) / (v * conj v), K.div_mem hs hv⟩ : ↥K)
        * Polynomial.X
      + Polynomial.C (⟨((u * conj v) * (conj u * v)) / ((v * conj v) * (v * conj v)),
          K.div_mem hp (K.mul_mem hv hv)⟩ : ↥K), ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun p => Polynomial.coeff p 2) h
    simp at h2
  · simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    show (u / v) ^ 2 - ((u * conj v + conj u * v) / (v * conj v)) * (u / v)
      + ((u * conj v) * (conj u * v)) / ((v * conj v) * (v * conj v)) = 0
    field_simp
    ring
