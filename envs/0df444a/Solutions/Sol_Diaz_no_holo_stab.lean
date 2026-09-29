-- Prove2me | solution 1 for Diaz.no_holo_stab
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:14:37.894935+00:00
-- url     : https://prove2.me/submissions/6fde44fd-09ad-4449-841f-82d9ed723611

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

theorem solution {K : Subfield ℂ} {z : ℂ} (hz : Transcendental K z)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hden : c * z + d ≠ 0) (h : (a * z + b) / (c * z + d) = z) :
    c = 0 ∧ b = 0 ∧ a = d := by
  have h' : a * z + b = z * (c * z + d) := by
    rw [div_eq_iff hden] at h
    linear_combination h
  have key : c * z ^ 2 + (d - a) * z + (-b) = 0 := by linear_combination -h'
  obtain ⟨h1, h2, h3⟩ := noquad_aux hz hc (sub_mem hd ha) (neg_mem hb) key
  exact ⟨h1, neg_eq_zero.mp h3, (sub_eq_zero.mp h2).symm⟩
