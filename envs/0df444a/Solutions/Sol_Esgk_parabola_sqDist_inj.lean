-- Prove2me | solution 1 for Esgk.parabola_sqDist_inj
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-16T23:25:28.623361+00:00
-- url     : https://prove2.me/submissions/086a5b57-4c10-47d8-87ad-3bd3be2541e6

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

Standalone submission artifact for the Prove2Me mission
"Superlinear or exact bounds for planar distinct distances".
Self-contained over Mathlib: integer parabola points have pairwise distinct
distances. Mirrors `Esgk.parabola_sqDist_inj` / `Esgk.parabola_descent` in
`lean/Esgk/Parabola.lean` of esgk-on3 (kernel-checked there on 2026-09-16).

Scope: supporting construction fact. It does not prove the superlinear
target and is not an exact determination of the extremal function.
-/

import Mathlib

/-- Descent step: distinct difference lengths force a strict `B > B` absurdity.
Given `d1 < d2` with `d1^2 * (1+s1^2) = d2^2 * (1+s2^2)`, write `d1 = g*u`,
`d2 = g*v` with `Coprime u v`. Coprimality aligns the cofactors to one value
`k`, so `(s1*u)^2 - (s2*v)^2 = v^2 - u^2`; with `A = s1*u - s2*v ≥ 1` this
gives `A * B = v^2 - u^2 < v^2 ≤ B` for `B = s1*u + s2*v`. -/
private theorem parabola_descent {d1 s1 d2 s2 : ℕ} (hs1 : d1 ≤ s1) (hs2 : d2 ≤ s2)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) (hlt : d1 < d2)
    (h : d1 ^ 2 * (1 + s1 ^ 2) = d2 ^ 2 * (1 + s2 ^ 2)) : False := by
  -- A smaller difference forces a larger sum.
  have hss : s2 < s1 := by
    by_contra hc
    have hc' : s1 ≤ s2 := not_lt.mp hc
    have e_le : d1 ^ 2 * (1 + s1 ^ 2) ≤ d1 ^ 2 * (1 + s2 ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Nat.add_le_add_left (Nat.pow_le_pow_left hc' 2) 1) (Nat.zero_le _)
    have e1 : d1 ^ 2 < d2 ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_lt_mul_self (Nat.zero_le _) hlt
    have e_lt : d1 ^ 2 * (1 + s2 ^ 2) < d2 ^ 2 * (1 + s2 ^ 2) :=
      mul_lt_mul_of_pos_right e1 (by positivity)
    omega
  -- Split off the gcd.
  have hg0 : 0 < Nat.gcd d1 d2 := by
    rcases Nat.eq_zero_or_pos (Nat.gcd d1 d2) with h0 | hpos
    · exfalso
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_left d1 d2
      rw [h0] at hk
      simp at hk
      omega
    · exact hpos
  obtain ⟨g, u, v, hg, hgu, hgv, hcop⟩ :
      ∃ g u v, 0 < g ∧ g * u = d1 ∧ g * v = d2 ∧ Nat.Coprime u v :=
    ⟨Nat.gcd d1 d2, d1 / Nat.gcd d1 d2, d2 / Nat.gcd d1 d2, hg0, by
      rw [mul_comm]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), by
      rw [mul_comm]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _),
      Nat.coprime_div_gcd_div_gcd hg0⟩
  have hu : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | hpos
    · exfalso; rw [h0, mul_zero] at hgu; omega
    · exact hpos
  have hv : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · exfalso; rw [h0, mul_zero] at hgv; omega
    · exact hpos
  -- Cancel `g^2` from the hypothesis.
  have heq : u ^ 2 * (1 + s1 ^ 2) = v ^ 2 * (1 + s2 ^ 2) := by
    have e1 : (g * u) ^ 2 * (1 + s1 ^ 2) = g ^ 2 * (u ^ 2 * (1 + s1 ^ 2)) := by ring
    have e2 : (g * v) ^ 2 * (1 + s2 ^ 2) = g ^ 2 * (v ^ 2 * (1 + s2 ^ 2)) := by ring
    rw [hgu] at e1
    rw [hgv] at e2
    have e : g ^ 2 * (u ^ 2 * (1 + s1 ^ 2)) = g ^ 2 * (v ^ 2 * (1 + s2 ^ 2)) := by
      rw [← e1, ← e2]; exact h
    exact mul_left_cancel₀ (ne_of_gt (pow_pos hg 2)) e
  -- Align the cofactors.
  have hcopvv : Nat.Coprime (v ^ 2) (u ^ 2) := hcop.symm.pow 2 2
  have hcopuu : Nat.Coprime (u ^ 2) (v ^ 2) := hcop.pow 2 2
  obtain ⟨k1, hk1⟩ : v ^ 2 ∣ 1 + s1 ^ 2 :=
    hcopvv.dvd_of_dvd_mul_left ⟨1 + s2 ^ 2, heq⟩
  obtain ⟨k2, hk2⟩ : u ^ 2 ∣ 1 + s2 ^ 2 :=
    hcopuu.dvd_of_dvd_mul_right ⟨1 + s1 ^ 2, by rw [mul_comm (1 + s2 ^ 2)]; exact heq.symm⟩
  have hk : k1 = k2 := by
    have e : (u ^ 2 * v ^ 2) * k1 = (u ^ 2 * v ^ 2) * k2 := by
      have h1 : (u ^ 2 * v ^ 2) * k1 = u ^ 2 * (v ^ 2 * k1) := by ring
      have h2 : (u ^ 2 * v ^ 2) * k2 = v ^ 2 * (u ^ 2 * k2) := by ring
      rw [h1, h2, ← hk1, ← hk2]
      exact heq
    have hpos : 0 < u ^ 2 * v ^ 2 := Nat.mul_pos (pow_pos hu 2) (pow_pos hv 2)
    exact mul_left_cancel₀ (ne_of_gt hpos) e
  -- The square identity, then the size contradiction.
  have key : (s1 * u) ^ 2 + u ^ 2 = (s2 * v) ^ 2 + v ^ 2 := by
    have h1 : (s1 * u) ^ 2 + u ^ 2 = u ^ 2 * (v ^ 2 * k1) := by rw [← hk1]; ring
    have h2 : (s2 * v) ^ 2 + v ^ 2 = v ^ 2 * (u ^ 2 * k2) := by rw [← hk2]; ring
    calc (s1 * u) ^ 2 + u ^ 2 = u ^ 2 * (v ^ 2 * k1) := h1
      _ = v ^ 2 * (u ^ 2 * k1) := by ring
      _ = v ^ 2 * (u ^ 2 * k2) := by rw [hk]
      _ = (s2 * v) ^ 2 + v ^ 2 := h2.symm
  have huv : u < v := by
    by_contra hc
    have hc' : v ≤ u := not_lt.mp hc
    have hle : g * v ≤ g * u := mul_le_mul_of_nonneg_left hc' (Nat.zero_le _)
    rw [hgu, hgv] at hle
    omega
  have hu2 : u ^ 2 < v ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_lt_mul_self (Nat.zero_le _) huv
  have hYX : s2 * v < s1 * u := by
    by_contra hc
    have hc' : s1 * u ≤ s2 * v := not_lt.mp hc
    have hle : (s1 * u) ^ 2 ≤ (s2 * v) ^ 2 := Nat.pow_le_pow_left hc' 2
    omega
  obtain ⟨A, hX⟩ : ∃ A, s1 * u = s2 * v + A := ⟨s1 * u - s2 * v, by omega⟩
  have hA1 : 1 ≤ A := by omega
  have key2 : A * ((s2 * v) + (s2 * v + A)) = v ^ 2 - u ^ 2 := by
    rw [hX] at key
    have hring : (s2 * v + A) ^ 2 = (s2 * v) ^ 2 + A * ((s2 * v) + (s2 * v + A)) := by ring
    omega
  have hu1 : 1 ≤ u := hu
  have hu21 : 1 ≤ u ^ 2 := by
    have hmm : (1 : ℕ) * 1 ≤ u * u := Nat.mul_le_mul hu1 hu1
    rwa [one_mul, ← pow_two] at hmm
  have hABlt : A * ((s2 * v) + (s2 * v + A)) < v * v := by
    have hrw : v * v = v ^ 2 := by ring
    omega
  have e_le1 : d2 * v ≤ s2 * v := mul_le_mul_of_nonneg_right hs2 (Nat.zero_le _)
  have e_eq : d2 * v = g * (v * v) := by rw [← hgv]; ring
  have e_ge : v * v ≤ g * (v * v) := by
    have hle : (1 : ℕ) * (v * v) ≤ g * (v * v) :=
      Nat.mul_le_mul (show 1 ≤ g by omega) le_rfl
    rwa [one_mul] at hle
  have hBgt : s2 * v < (s2 * v + A) + (s2 * v) := by omega
  have hABge : (s2 * v) + (s2 * v + A) ≤ A * ((s2 * v) + (s2 * v + A)) :=
    le_mul_of_one_le_left (Nat.zero_le _) hA1
  omega


/-- Squared distance key: `(a-b)^2 * (1+(a+b)^2)` determines the unordered pair.
For `b < a` and `d < c`, equal values force `a = c ∧ b = d`. Hence distinct
nonnegative integer points `(t, t^2)` have pairwise distinct distances. -/
theorem solution {a b c d : ℕ} (hab : b < a) (hcd : d < c)
    (h : (a - b) ^ 2 * (1 + (a + b) ^ 2) = (c - d) ^ 2 * (1 + (c + d) ^ 2)) :
    a = c ∧ b = d := by
  have hs1 : a - b ≤ a + b := by omega
  have hs2 : c - d ≤ c + d := by omega
  have hd1 : 1 ≤ a - b := by omega
  have hd2 : 1 ≤ c - d := by omega
  rcases lt_trichotomy (a - b) (c - d) with hlt | heq | hgt
  · exact (parabola_descent hs1 hs2 hd1 hd2 hlt h).elim
  · rw [heq] at h
    have hcan : 1 + (a + b) ^ 2 = 1 + (c + d) ^ 2 :=
      mul_left_cancel₀ (by positivity : (c - d) ^ 2 ≠ 0) h
    have h2 : (a + b) ^ 2 = (c + d) ^ 2 := by omega
    have hs : a + b = c + d := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hlt2 := mul_self_lt_mul_self (Nat.zero_le _) hlt
        rw [← pow_two, ← pow_two] at hlt2
        omega
      · have hlt2 := mul_self_lt_mul_self (Nat.zero_le _) hgt
        rw [← pow_two, ← pow_two] at hlt2
        omega
    exact ⟨by omega, by omega⟩
  · exact (parabola_descent hs2 hs1 hd2 hd1 hgt h.symm).elim

