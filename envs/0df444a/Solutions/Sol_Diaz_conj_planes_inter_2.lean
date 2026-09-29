-- Prove2me | solution 2 for Diaz.conj_planes_inter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:18:31.599967+00:00
-- url     : https://prove2.me/submissions/a5dbd5b1-3662-4e76-9fc1-0ecfb342f5c9

/-
`Diaz.conj_planes_inter` is `Diaz.indep_three` rearranged: the equation
`A + B u = C + D ū` is `(A - C) + B·u + (-D)·ū = 0`, and independence of
`1, u, ū` over `K` gives all three coefficients zero.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_indep_three

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental (↥K) u) (hρ : u * conj u ∈ K)
    {A B C D : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K) (hD : D ∈ K)
    (h : A + B * u = C + D * conj u) : B = 0 ∧ D = 0 ∧ A = C := by
  have hrel : (A - C) + B * u + (-D) * conj u = 0 := by linear_combination h
  obtain ⟨h1, h2, h3⟩ :=
    Diaz.indep_three hT hρ (K.sub_mem hA hC) hB (K.neg_mem hD) hrel
  exact ⟨h2, neg_eq_zero.mp h3, sub_eq_zero.mp h1⟩
