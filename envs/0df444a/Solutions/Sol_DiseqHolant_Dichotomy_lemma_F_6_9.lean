-- Prove2me | solution 1 for DiseqHolant.Dichotomy.lemma_F_6_9
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T15:19:59.638611+00:00
-- url     : https://prove2.me/submissions/f7289caf-fc6a-48fc-8e8d-1c7d5f26ffc1

import Mathlib

set_option autoImplicit false

open Polynomial

private lemma coeff_linear_pow (c d : ℂ) (m j : ℕ) (hj : j ≤ m) :
    (((C c + C d * X : ℂ[X])) ^ m).coeff j = c ^ (m - j) * d ^ j * (m.choose j : ℂ) := by
  have key : ((C c + C d * X : ℂ[X])) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        C (c ^ k) * (C (d ^ (m - k)) * X ^ (m - k)) * ((m.choose k : ℕ) : ℂ[X]) := by
    rw [add_pow]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [C_pow, mul_pow]
  rw [key, Polynomial.finsetSum_coeff, Finset.sum_eq_single (m - j)]
  · have hjm : m - (m - j) = j := by omega
    rw [hjm, Nat.choose_symm hj]
    rw [Polynomial.coeff_mul_natCast, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow_self, mul_one]
  · intro k hk hkj
    have hk' : k ≤ m := by
      simp only [Finset.mem_range] at hk
      omega
    have hne : j ≠ m - k := by omega
    rw [Polynomial.coeff_mul_natCast, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, if_neg hne]
    simp
  · intro h
    exfalso
    apply h
    simp only [Finset.mem_range]
    omega

theorem solution (m : ℕ) (hm : 3 ≤ m) (a b c d : ℂ) (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hperm : Set.BijOn (fun z : ℂ => (c + d * z) / (a + b * z))
      {z : ℂ | z ^ m = 1} {z : ℂ | z ^ m = 1}) :
    ∃ α : ℂ, α ^ m = 1 ∧ ((b = 0 ∧ c = 0 ∧ d = α * a) ∨ (a = 0 ∧ d = 0 ∧ c = α * b)) := by
  classical
  have hm0 : 0 < m := by omega
  set S : Finset ℂ := nthRootsFinset m 1 with hSdef
  set P : ℂ[X] := (C c + C d * X) ^ m - (C a + C b * X) ^ m with hPdef
  -- Step 1: P vanishes on the m-th roots of unity
  have hroot : ∀ z ∈ S, P.IsRoot z := by
    intro z hz
    have hzpow : z ^ m = 1 := by
      rw [hSdef] at hz
      rwa [mem_nthRootsFinset hm0] at hz
    have hφmem : ((c + d * z) / (a + b * z)) ^ m = 1 := hperm.mapsTo hzpow
    have hzden : (a + b * z) ^ m ≠ 0 := pow_ne_zero m (hpole z hzpow)
    have heq : (c + d * z) ^ m = (a + b * z) ^ m := by
      rw [div_pow, div_eq_one_iff_eq hzden] at hφmem
      exact hφmem
    have hval : eval z P = (c + d * z) ^ m - (a + b * z) ^ m := by
      simp [hPdef]
    show eval z P = 0
    rw [hval, heq, sub_self]
  -- Step 2: X^m - 1 divides P
  have hdvd : (X ^ m - 1 : ℂ[X]) ∣ P := by
    have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / m)) m :=
      Complex.isPrimitiveRoot_exp m hm0.ne'
    rw [X_pow_sub_one_eq_prod (ζ := Complex.exp (2 * Real.pi * Complex.I / m)) hm0 hζ]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i _ j _ hij
      simpa using pairwise_coprime_X_sub_C (K := ℂ) (s := fun z : ℂ => z) Function.injective_id hij
    · intro i hi
      exact dvd_iff_isRoot.mpr (hroot i (by rwa [hSdef]))
  -- Step 3: P is a constant multiple of X^m - 1
  have hPform : ∃ k : ℂ, P = C k * (X ^ m - 1) := by
    by_cases hP0 : P = 0
    · exact ⟨0, by rw [hP0]; simp⟩
    · obtain ⟨Q, hQ⟩ := hdvd
      have hXnat : (X ^ m - 1 : ℂ[X]).natDegree = m := by
        simpa using natDegree_X_pow_sub_C (R := ℂ) (n := m) (r := (1 : ℂ))
      have hXne : (X ^ m - 1 : ℂ[X]) ≠ 0 := by
        intro h
        rw [h, Polynomial.natDegree_zero] at hXnat
        omega
      have hQne : Q ≠ 0 := by
        intro hQ0
        apply hP0
        rw [hQ, hQ0, mul_zero]
      have hdeg_base : ∀ x y : ℂ, (C x + C y * X : ℂ[X]).natDegree ≤ 1 := by
        intro x y
        calc (C x + C y * X : ℂ[X]).natDegree
            ≤ max (C x).natDegree (C y * X).natDegree := natDegree_add_le _ _
          _ ≤ 1 := by
              apply max_le
              · simp
              · calc (C y * X : ℂ[X]).natDegree ≤ (C y).natDegree + X.natDegree :=
                    natDegree_mul_le
                  _ = 1 := by simp
      have hdeg_pow : ∀ x y : ℂ, ((C x + C y * X : ℂ[X]) ^ m).natDegree ≤ m := by
        intro x y
        calc ((C x + C y * X : ℂ[X]) ^ m).natDegree
            ≤ m * (C x + C y * X : ℂ[X]).natDegree := natDegree_pow_le
          _ ≤ m * 1 := Nat.mul_le_mul_left m (hdeg_base x y)
          _ = m := Nat.mul_one m
      have hPdeg : P.natDegree ≤ m := by
        rw [hPdef]
        calc ((C c + C d * X) ^ m - (C a + C b * X) ^ m).natDegree
            ≤ max ((C c + C d * X) ^ m).natDegree ((C a + C b * X) ^ m).natDegree :=
              natDegree_sub_le _ _
          _ ≤ m := max_le (hdeg_pow c d) (hdeg_pow a b)
      have hmul : P.natDegree = m + Q.natDegree := by
        rw [hQ, natDegree_mul hXne hQne, hXnat]
      have hQdeg : Q.natDegree = 0 := by omega
      refine ⟨Q.coeff 0, ?_⟩
      have hQc : Q = C (Q.coeff 0) := eq_C_of_natDegree_le_zero (by omega : Q.natDegree ≤ 0)
      calc P = (X ^ m - 1) * Q := hQ
        _ = (X ^ m - 1) * C (Q.coeff 0) := by
              conv_lhs => rw [hQc]
        _ = C (Q.coeff 0) * (X ^ m - 1) := by ring
  -- Step 4: coefficient relations
  obtain ⟨k, hk⟩ := hPform
  have hcoef : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → c ^ (m - j) * d ^ j = a ^ (m - j) * b ^ j := by
    intro j hj1 hj2
    have hjm : j ≤ m := by omega
    have hne0 : j ≠ 0 := by omega
    have hnem : j ≠ m := by omega
    have hleft : P.coeff j = (c ^ (m - j) * d ^ j - a ^ (m - j) * b ^ j) * (m.choose j : ℂ) := by
      rw [hPdef, Polynomial.coeff_sub, coeff_linear_pow c d m j hjm,
        coeff_linear_pow a b m j hjm]
      ring
    have hright : (C k * (X ^ m - 1) : ℂ[X]).coeff j = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_one, if_neg hne0, if_neg hnem]
      ring
    have h0 : (c ^ (m - j) * d ^ j - a ^ (m - j) * b ^ j) * (m.choose j : ℂ) = 0 := by
      rw [← hleft, hk, hright]
    have hch : (m.choose j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hjm)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hch)
  -- Step 5: alpha = phi(1) is a root of unity
  have hφ1 : ((c + d * 1) / (a + b * 1)) ^ m = 1 := by
    have h1set : (1 : ℂ) ∈ {z : ℂ | z ^ m = 1} := by simp
    exact hperm.mapsTo h1set
  set α : ℂ := (c + d * 1) / (a + b * 1) with hαdef
  have hα : α ^ m = 1 := by
    rw [hαdef]
    exact hφ1
  -- Step 6: case analysis
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      intro ha0
      apply hdet
      rw [ha0, hb]
      ring
    have hd : d ≠ 0 := by
      intro hd0
      apply hdet
      rw [hb, hd0]
      ring
    have hrel : c ^ (m - 1) * d = 0 := by
      simpa only [hb, pow_one, mul_zero] using hcoef 1 le_rfl (by omega : 1 ≤ m - 1)
    have hc : c = 0 := by
      rcases mul_eq_zero.mp hrel with h | h
      · exact (pow_eq_zero_iff (by omega : m - 1 ≠ 0)).mp h
      · exact absurd h hd
    refine ⟨α, hα, Or.inl ⟨hb, hc, ?_⟩⟩
    rw [hαdef]
    simp only [hb, hc, zero_add, mul_one, add_zero]
    rw [div_mul_cancel₀ d ha]
  · by_cases ha : a = 0
    · have hb0 : b ≠ 0 := by
        intro hb0
        apply hdet
        rw [ha, hb0]
        ring
      have hc : c ≠ 0 := by
        intro hc0
        apply hdet
        rw [ha, hc0]
        ring
      have hrel : c * d ^ (m - 1) = 0 := by
        simpa only [show m - (m - 1) = 1 by omega, ha, pow_one, zero_mul] using
          hcoef (m - 1) (by omega : 1 ≤ m - 1) le_rfl
      have hd : d = 0 := by
        rcases mul_eq_zero.mp hrel with h | h
        · exact absurd h hc
        · exact (pow_eq_zero_iff (by omega : m - 1 ≠ 0)).mp h
      refine ⟨α, hα, Or.inr ⟨ha, hd, ?_⟩⟩
      rw [hαdef]
      simp only [ha, hd, zero_add, mul_one, add_zero]
      rw [div_mul_cancel₀ c hb0]
    · have hrel1 : c ^ (m - 1) * d = a ^ (m - 1) * b := by
        simpa only [pow_one] using hcoef 1 le_rfl (by omega : 1 ≤ m - 1)
      have hrel2 : c ^ (m - 2) * d ^ 2 = a ^ (m - 2) * b ^ 2 :=
        hcoef 2 (by omega) (by omega : 2 ≤ m - 1)
      have hc : c ≠ 0 := by
        intro hc0
        rw [hc0] at hrel1
        simp only [zero_pow (by omega : m - 1 ≠ 0), zero_mul] at hrel1
        rcases mul_eq_zero.mp hrel1.symm with h | h
        · exact ha ((pow_eq_zero_iff (by omega : m - 1 ≠ 0)).mp h)
        · exact hb h
      have hd : d ≠ 0 := by
        intro hd0
        rw [hd0, mul_zero] at hrel1
        rcases mul_eq_zero.mp hrel1.symm with h | h
        · exact ha ((pow_eq_zero_iff (by omega : m - 1 ≠ 0)).mp h)
        · exact hb h
      have h1' : c ^ (m - 1) * d * b = c ^ (m - 2) * d ^ 2 * a := by
        have hapow : a ^ (m - 1) = a ^ (m - 2) * a := by
          rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
        rw [hrel1, hrel2, hapow]
        ring
      have hkey : c ^ (m - 2) * d * (c * b) = c ^ (m - 2) * d * (d * a) := by
        calc c ^ (m - 2) * d * (c * b) = c ^ (m - 1) * d * b := by
              rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
              ring
          _ = c ^ (m - 2) * d ^ 2 * a := h1'
          _ = c ^ (m - 2) * d * (d * a) := by ring
      have hcancel : c * b = d * a :=
        mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (m - 2) hc) hd) hkey
      have hbc : b * c = a * d := by
        rw [mul_comm b c, hcancel, mul_comm d a]
      exact absurd (by rw [hbc]; ring : a * d - b * c = 0) hdet
