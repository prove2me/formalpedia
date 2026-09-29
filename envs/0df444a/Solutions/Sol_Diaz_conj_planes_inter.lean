-- Prove2me | solution 1 for Diaz.conj_planes_inter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:54.940416+00:00
-- url     : https://prove2.me/submissions/32f573ae-8e68-41b4-baba-3f9538ef3ac6

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental (↥K) u) (hρ : u * conj u ∈ K)
    {A B C D : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K) (hD : D ∈ K)
    (h : A + B * u = C + D * conj u) : B = 0 ∧ D = 0 ∧ A = C := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hT (isAlgebraic_zero)
  have hcu : conj u ≠ 0 := by simpa using hu0
  have hrel : B * u ^ 2 + (A - C) * u + (-D * (u * conj u)) = 0 := by
    linear_combination u * h
  set P : Polynomial ↥K :=
    Polynomial.C (⟨B, hB⟩ : ↥K) * Polynomial.X ^ 2
      + Polynomial.C (⟨A - C, K.sub_mem hA hC⟩ : ↥K) * Polynomial.X
      + Polynomial.C (⟨-D * (u * conj u), K.mul_mem (K.neg_mem hD) hρ⟩ : ↥K) with hPdef
  have haev : Polynomial.aeval u P = 0 := by
    simp only [hPdef, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    show B * u ^ 2 + (A - C) * u + (-D * (u * conj u)) = 0
    exact hrel
  have hP0 : P = 0 := by
    by_contra hne
    exact hT ⟨P, hne, haev⟩
  have hB0 : B = 0 := by
    have hc := congrArg (fun p => Polynomial.coeff p 2) hP0
    simp only [hPdef] at hc
    simp [Polynomial.coeff_C, Polynomial.coeff_X, Subtype.ext_iff] at hc
    exact hc
  have hAC : A - C = 0 := by
    have hc := congrArg (fun p => Polynomial.coeff p 1) hP0
    simp only [hPdef] at hc
    simp [Polynomial.coeff_C, Polynomial.coeff_X, Subtype.ext_iff] at hc
    exact hc
  have hD0 : D = 0 := by
    have : D * conj u = 0 := by linear_combination -h + hAC + u * hB0
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hcu
  exact ⟨hB0, hD0, sub_eq_zero.mp hAC⟩
