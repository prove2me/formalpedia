-- Prove2me | solution 1 for Diaz.det_pencil_eq_conic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:45.494605+00:00
-- url     : https://prove2.me/submissions/38b756ef-30bb-4597-9f57-40e4dd0e9852

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

theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) (A B C : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, A i j ∈ K) (hB : ∀ i j, B i j ∈ K) (hC : ∀ i j, C i j ∈ K)
    (hdet : (A + u • B + (conj u) • C).det = 0) :
    ∃ c : ℂ, c ∈ K ∧ ∀ x y z : ℂ,
      (x • A + y • B + z • C).det = c * (y * z - (u * conj u) * x ^ 2) := by
  classical
  have hcu : conj u ≠ 0 := by simpa using hu0
  set ρ : ℂ := u * conj u with hρdef
  have hρ0 : ρ ≠ 0 := mul_ne_zero hu0 hcu
  have hconj : conj u = ρ / u := by rw [hρdef]; field_simp
  set dA : ℂ := A 0 0 * A 1 1 - A 0 1 * A 1 0 with hdA
  set dB : ℂ := B 0 0 * B 1 1 - B 0 1 * B 1 0 with hdB
  set dC : ℂ := C 0 0 * C 1 1 - C 0 1 * C 1 0 with hdC
  set bAB : ℂ := A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0 with hbAB
  set bAC : ℂ := A 0 0 * C 1 1 + C 0 0 * A 1 1 - A 0 1 * C 1 0 - C 0 1 * A 1 0 with hbAC
  set bBC : ℂ := B 0 0 * C 1 1 + C 0 0 * B 1 1 - B 0 1 * C 1 0 - C 0 1 * B 1 0 with hbBC
  have expand : ∀ x y z : ℂ, (x • A + y • B + z • C).det
      = x ^ 2 * dA + y ^ 2 * dB + z ^ 2 * dC + x * y * bAB + x * z * bAC + y * z * bBC := by
    intro x y z
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hdA, hdB, hdC, hbAB, hbAC, hbBC]
    ring
  have hd0 : dA + u ^ 2 * dB + (conj u) ^ 2 * dC + u * bAB + (conj u) * bAC + ρ * bBC = 0 := by
    have := expand 1 u (conj u)
    simp only [one_smul, one_pow, one_mul, mul_one] at this
    rw [this] at hdet
    rw [hρdef]
    linear_combination hdet
  set k : ℕ → ℂ := fun j =>
    if j = 0 then ρ ^ 2 * dC else if j = 1 then ρ * bAC else if j = 2 then dA + ρ * bBC
      else if j = 3 then bAB else if j = 4 then dB else 0 with hk
  have hkK : ∀ j, k j ∈ K := by
    have hdAK : dA ∈ K := K.sub_mem (K.mul_mem (hA 0 0) (hA 1 1)) (K.mul_mem (hA 0 1) (hA 1 0))
    have hdBK : dB ∈ K := K.sub_mem (K.mul_mem (hB 0 0) (hB 1 1)) (K.mul_mem (hB 0 1) (hB 1 0))
    have hdCK : dC ∈ K := K.sub_mem (K.mul_mem (hC 0 0) (hC 1 1)) (K.mul_mem (hC 0 1) (hC 1 0))
    have hbABK : bAB ∈ K :=
      K.sub_mem (K.sub_mem (K.add_mem (K.mul_mem (hA 0 0) (hB 1 1)) (K.mul_mem (hB 0 0) (hA 1 1)))
        (K.mul_mem (hA 0 1) (hB 1 0))) (K.mul_mem (hB 0 1) (hA 1 0))
    have hbACK : bAC ∈ K :=
      K.sub_mem (K.sub_mem (K.add_mem (K.mul_mem (hA 0 0) (hC 1 1)) (K.mul_mem (hC 0 0) (hA 1 1)))
        (K.mul_mem (hA 0 1) (hC 1 0))) (K.mul_mem (hC 0 1) (hA 1 0))
    have hbBCK : bBC ∈ K :=
      K.sub_mem (K.sub_mem (K.add_mem (K.mul_mem (hB 0 0) (hC 1 1)) (K.mul_mem (hC 0 0) (hB 1 1)))
        (K.mul_mem (hB 0 1) (hC 1 0))) (K.mul_mem (hC 0 1) (hB 1 0))
    intro j
    simp only [hk]
    split_ifs
    · exact K.mul_mem (K.pow_mem hρ 2) hdCK
    · exact K.mul_mem hρ hbACK
    · exact K.add_mem hdAK (K.mul_mem hρ hbBCK)
    · exact hbABK
    · exact hdBK
    · exact K.zero_mem
  have hsum : ∑ j ∈ Finset.range 5, k j * u ^ j = 0 := by
    have hd1 : ρ ^ 2 * dC + ρ * bAC * u + (dA + ρ * bBC) * u ^ 2 + bAB * u ^ 3 + dB * u ^ 4
        = 0 := by
      linear_combination u ^ 2 * hd0 + (dC * (ρ + u * conj u) + bAC * u) * hρdef
    simp only [hk, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linear_combination hd1
  have hzero := aux_powers_indep hT 5 k hkK hsum
  have e0 : ρ ^ 2 * dC = 0 := by simpa [hk] using hzero 0 (by norm_num)
  have e1 : ρ * bAC = 0 := by simpa [hk] using hzero 1 (by norm_num)
  have e2 : dA + ρ * bBC = 0 := by simpa [hk] using hzero 2 (by norm_num)
  have e3 : bAB = 0 := by simpa [hk] using hzero 3 (by norm_num)
  have e4 : dB = 0 := by simpa [hk] using hzero 4 (by norm_num)
  have hdC0 : dC = 0 := by
    rcases mul_eq_zero.mp e0 with hzz | hzz
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzz) hρ0
    · exact hzz
  have hbAC0 : bAC = 0 := by
    rcases mul_eq_zero.mp e1 with hzz | hzz
    · exact absurd hzz hρ0
    · exact hzz
  refine ⟨bBC, ?_, ?_⟩
  · exact K.sub_mem (K.sub_mem (K.add_mem (K.mul_mem (hB 0 0) (hC 1 1))
      (K.mul_mem (hC 0 0) (hB 1 1))) (K.mul_mem (hB 0 1) (hC 1 0))) (K.mul_mem (hC 0 1) (hB 1 0))
  · intro x y z
    rw [expand x y z, e3, e4, hdC0, hbAC0]
    linear_combination (x ^ 2) * e2
