-- Prove2me | solution 1 for Diaz.indep_of_algebraic_product
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:12:03.422782+00:00
-- url     : https://prove2.me/submissions/c497890a-d2dc-4518-9cba-3027346cc5f7

import Mathlib

open ComplexConjugate

/-- Auxiliary: a transcendental element satisfies no non-trivial quadratic over the base. -/
private theorem noquad_aux {K : Subfield ℂ} {p : ℂ} (hp : Transcendental K p)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (h : a * p ^ 2 + b * p + c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  rw [transcendental_iff_injective] at hp
  have hP : (Polynomial.C (⟨a, ha⟩ : K) * Polynomial.X ^ 2
      + Polynomial.C (⟨b, hb⟩ : K) * Polynomial.X
      + Polynomial.C (⟨c, hc⟩ : K) : Polynomial K) = 0 := by
    apply hp
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_zero]
    exact_mod_cast h
  have h2 := congrArg (fun q => Polynomial.coeff q 2) hP
  have h1 := congrArg (fun q => Polynomial.coeff q 1) hP
  have h0 := congrArg (fun q => Polynomial.coeff q 0) hP
  simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X] at h2 h1 h0
  exact ⟨congrArg Subtype.val h2, congrArg Subtype.val h1, congrArg Subtype.val h0⟩

theorem solution {K : Subfield ℂ} {p ν : ℂ}
    (hp : Transcendental K p) (hβ : p * ν ∈ K) (hβ0 : p * ν ≠ 0)
    {A B C : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K)
    (h : A + B * ν + C * p = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have key : C * p ^ 2 + A * p + B * (p * ν) = 0 := by linear_combination p * h
  obtain ⟨h1, h2, h3⟩ := noquad_aux hp hC hA (mul_mem hB hβ) key
  refine ⟨h2, ?_, h1⟩
  rcases mul_eq_zero.mp h3 with hb | hpv
  · exact hb
  · exact absurd hpv hβ0
