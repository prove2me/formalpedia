-- Prove2me | solution 1 for Diaz.forced_plane_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:40.056718+00:00
-- url     : https://prove2.me/submissions/98def6d7-20d0-41e2-8fb0-fc14a2dd07a1

import Mathlib

open ComplexConjugate

theorem aux_powers_indep {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (n : ℕ)
    (k : ℕ → ℂ) (hk : ∀ i, k i ∈ K)
    (h : ∑ i ∈ Finset.range n, k i * u ^ i = 0) :
    ∀ i ∈ Finset.range n, k i = 0 := by
  classical
  set P : Polynomial K :=
    ∑ i ∈ Finset.range n, Polynomial.C (⟨k i, hk i⟩ : K) * Polynomial.X ^ i with hPdef
  have hev : Polynomial.aeval u P = 0 := by
    rw [hPdef]
    simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    rw [← h]
    rfl
  have hP : P = 0 := by
    by_contra hne
    exact hT ⟨P, hne, hev⟩
  intro i hi
  have hc : P.coeff i = 0 := by rw [hP]; simp
  rw [hPdef] at hc
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero] at hc
  rw [Finset.sum_ite_eq, if_pos hi] at hc
  simpa using congrArg (fun z : K => (z : ℂ)) hc

theorem aux_binary_form {K : Subfield ℂ} {x y : ℂ} (hy : y ≠ 0)
    (hxy : Transcendental K (x / y)) (d : ℕ) (c : ℕ → ℂ) (hc : ∀ i, c i ∈ K)
    (h : ∑ i ∈ Finset.range (d + 1), c i * x ^ i * y ^ (d - i) = 0) :
    ∀ i ∈ Finset.range (d + 1), c i = 0 := by
  refine aux_powers_indep hxy (d + 1) c hc ?_
  have hyd : (y : ℂ) ^ d ≠ 0 := pow_ne_zero _ hy
  apply mul_left_cancel₀ hyd
  rw [mul_zero, Finset.mul_sum, ← h]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hle : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [div_pow, pow_sub₀ y hy hle]
  field_simp

theorem aux_algebraMap_mk (K : Subfield ℂ) (a : ℂ) (h : a ∈ K) :
    (algebraMap (↥K) ℂ) ⟨a, h⟩ = a := rfl

theorem aux_ratio_transcendental {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) : Transcendental K (u / conj u) := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  intro halg
  have h1 : (u / conj u) ∈ algebraicClosure (↥K) ℂ := mem_algebraicClosure_iff.2 halg
  have h2 : (u * conj u) ∈ algebraicClosure (↥K) ℂ := by
    refine mem_algebraicClosure_iff.2 ⟨Polynomial.X - Polynomial.C ⟨u * conj u, hρ⟩, ?_, ?_⟩
    · exact Polynomial.X_sub_C_ne_zero _
    · rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        aux_algebraMap_mk, sub_self]
  have h3 : u ^ 2 ∈ algebraicClosure (↥K) ℂ := by
    have he : u ^ 2 = (u / conj u) * (u * conj u) := by field_simp <;> ring
    rw [he]; exact mul_mem h1 h2
  exact hT (IsAlgebraic.of_pow (by norm_num) (mem_algebraicClosure_iff.1 h3))

theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u)
    (hu0 : u ≠ 0) (hρ : u * conj u ∈ K) (d : ℕ) (c : ℕ → ℂ) (hc : ∀ i, c i ∈ K)
    (h : ∑ i ∈ Finset.range (d + 1), c i * u ^ i * (conj u) ^ (d - i) = 0) :
    ∀ i ∈ Finset.range (d + 1), c i = 0 := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  exact aux_binary_form hcu (aux_ratio_transcendental hT hu0 hρ) d c hc h
