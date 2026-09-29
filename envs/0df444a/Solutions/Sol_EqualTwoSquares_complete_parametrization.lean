-- Prove2me | solution 1 for EqualTwoSquares.complete_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:20:17.816953+00:00
-- url     : https://prove2.me/submissions/187354ab-f012-40e9-9645-6886fb472a92

-- Public-mission submission for EqualTwoSquares.complete_parametrization.
--
-- The three ingredients (parity alignment, the half-sum substitution, and the factorisation
-- of XY = UV) are proved inline, because a submission is a single self-contained file.

import Mathlib

theorem solution {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (∃ p q r s : ℤ,
      a = p * r + q * s ∧ b = p * s - q * r ∧
        c = p * r - q * s ∧ d = p * s + q * r) ∨
      (∃ p q r s : ℤ,
        a = p * r + q * s ∧ b = p * s - q * r ∧
          d = p * r - q * s ∧ c = p * s + q * r) := by
  -- ------------------------------------------------------------------ parity
  have parity (a b c d : ℤ) (h : a^2 + b^2 = c^2 + d^2) :
      (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by
    have ee {x y : ℤ} (hx : Even x) (hy : Even y) : Even (x - y) := by
      rcases hx with ⟨i, hi⟩
      rcases hy with ⟨j, hj⟩
      use i - j
      omega
    have oo {x y : ℤ} (hx : Odd x) (hy : Odd y) : Even (x - y) := by
      rcases hx with ⟨i, hi⟩
      rcases hy with ⟨j, hj⟩
      use i - j
      omega
    have sqmod4_even {x : ℤ} (hx : Even x) : (4 : ℤ) ∣ x^2 := by
      rcases hx with ⟨k, hk⟩
      use k^2
      rw [hk]
      ring
    have sqmod4_odd {x : ℤ} (hx : Odd x) : (4 : ℤ) ∣ x^2 - 1 := by
      rcases hx with ⟨k, hk⟩
      use k * (k + 1)
      rw [hk]
      ring
    have clash (rx ry rz rw : ℤ)
        (ha4 : (4 : ℤ) ∣ a^2 - rx) (hb4 : (4 : ℤ) ∣ b^2 - ry)
        (hc4 : (4 : ℤ) ∣ c^2 - rz) (hd4 : (4 : ℤ) ∣ d^2 - rw)
        (hneq : rx + ry ≠ rz + rw)
        (hsmall : -4 < rz + rw - rx - ry ∧ rz + rw - rx - ry < 4) : False := by
      have hdiv : (4 : ℤ) ∣ (a^2 - rx) + (b^2 - ry) - (c^2 - rz) - (d^2 - rw) :=
        dvd_sub (dvd_sub (dvd_add ha4 hb4) hc4) hd4
      have hval : (a^2 - rx) + (b^2 - ry) - (c^2 - rz) - (d^2 - rw) = rz + rw - rx - ry := by
        nlinarith
      rw [hval] at hdiv
      rcases hdiv with ⟨t, ht⟩
      omega
    rcases Int.even_or_odd a with ha | ha <;>
    rcases Int.even_or_odd b with hb | hb <;>
    rcases Int.even_or_odd c with hc | hc <;>
    rcases Int.even_or_odd d with hd | hd
    · exact Or.inl ⟨ee ha hc, ee hb hd⟩
    · exfalso
      exact clash 0 0 0 1 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
        (by simpa using sqmod4_even hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 0 0 1 0 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
        (sqmod4_odd hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 0 0 1 1 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
        (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 0 1 0 0 (by simpa using sqmod4_even ha) (sqmod4_odd hb)
        (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exact Or.inl ⟨ee ha hc, oo hb hd⟩
    · exact Or.inr ⟨ee ha hd, oo hb hc⟩
    · exfalso
      exact clash 0 1 1 1 (by simpa using sqmod4_even ha) (sqmod4_odd hb)
        (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 0 0 0 (sqmod4_odd ha) (by simpa using sqmod4_even hb)
        (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exact Or.inr ⟨oo ha hd, ee hb hc⟩
    · exact Or.inl ⟨oo ha hc, ee hb hd⟩
    · exfalso
      exact clash 1 0 1 1 (sqmod4_odd ha) (by simpa using sqmod4_even hb)
        (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 1 0 0 (sqmod4_odd ha) (sqmod4_odd hb)
        (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 1 0 1 (sqmod4_odd ha) (sqmod4_odd hb)
        (by simpa using sqmod4_even hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 1 1 0 (sqmod4_odd ha) (sqmod4_odd hb)
        (sqmod4_odd hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exact Or.inl ⟨oo ha hc, oo hb hd⟩
  -- ------------------------------------------------------------------ halves
  have halves (a b c d : ℤ) (h : a^2 + b^2 = c^2 + d^2)
      (hac : Even (a - c)) (hbd : Even (b - d)) :
      ∃ X Y U V : ℤ,
        X + Y = a ∧ X - Y = c ∧ U - V = b ∧ U + V = d ∧ X * Y = U * V := by
    rcases hac with ⟨k, hk⟩
    rcases hbd with ⟨l, hl⟩
    have hc : c = a - 2 * k := by linarith
    have hd : d = b - 2 * l := by linarith
    rw [hc, hd] at h ⊢
    refine ⟨a - k, k, b - l, -l, ?_, ?_, ?_, ?_, ?_⟩
    · ring
    · ring
    · ring
    · ring
    · nlinarith
  -- ------------------------------------------------------------------ factor
  have factor (X Y U V : ℤ) (h : X * Y = U * V) :
      ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by
    by_cases hX : X = 0
    · by_cases hU : U = 0
      · refine ⟨0, 1, V, Y, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hU]
      · have hV : V = 0 := by
          have h' := h
          rw [hX] at h'
          have hUV : U * V = 0 := by simpa using h'.symm
          exact (mul_eq_zero.mp hUV).resolve_left hU
        refine ⟨U, Y, 0, 1, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hV]
    · by_cases hU : U = 0
      · have hY : Y = 0 := by
          have h' := h
          rw [hU] at h'
          have hXY : X * Y = 0 := by simpa using h'
          exact (mul_eq_zero.mp hXY).resolve_left hX
        refine ⟨X, V, 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [hU, hY]
      · have hgpos : 0 < Int.gcd X U := Int.gcd_pos_of_ne_zero_left U hX
        let g : ℤ := (Int.gcd X U : ℤ)
        obtain ⟨r, s, hcop, hXeq0, hUeq0⟩ := Int.exists_gcd_one (m := X) (n := U) hgpos
        have hXeq : X = r * g := by simpa [g] using hXeq0
        have hUeq : U = s * g := by simpa [g] using hUeq0
        have hgne : g ≠ 0 := by
          dsimp [g]
          exact_mod_cast (ne_of_gt hgpos)
        have hmul : g * (r * Y) = g * (s * V) := by
          calc
            g * (r * Y) = (r * g) * Y := by ring
            _ = X * Y := by rw [← hXeq]
            _ = U * V := h
            _ = (s * g) * V := by rw [hUeq]
            _ = g * (s * V) := by ring
        have hrY : r * Y = s * V := mul_left_cancel₀ hgne hmul
        have hr_ne : r ≠ 0 := by
          intro hr
          apply hX
          calc
            X = r * g := hXeq
            _ = 0 := by rw [hr]; ring
        have hs_ne : s ≠ 0 := by
          intro hs
          apply hU
          calc
            U = s * g := hUeq
            _ = 0 := by rw [hs]; ring
        have hbez : (1 : ℤ) = r * Int.gcdA r s + s * Int.gcdB r s := by
          have := Int.gcd_eq_gcd_ab r s
          simpa [hcop] using this
        have hsry : s ∣ r * Y := ⟨V, hrY⟩
        have hrsv : r ∣ s * V := ⟨Y, hrY.symm⟩
        have hsY : s ∣ Y := by
          have h1 : s ∣ (r * Y) * Int.gcdA r s := dvd_mul_of_dvd_left hsry _
          have h2 : s ∣ s * (Y * Int.gcdB r s) := dvd_mul_right s _
          have hsum := dvd_add h1 h2
          have heq : (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) = Y := by
            calc
              (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) =
                  Y * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
              _ = Y * 1 := by rw [hbez]
              _ = Y := by ring
          rwa [heq] at hsum
        have hrV : r ∣ V := by
          have h1 : r ∣ r * (V * Int.gcdA r s) := dvd_mul_right r _
          have h2 : r ∣ (s * V) * Int.gcdB r s := dvd_mul_of_dvd_left hrsv _
          have hsum := dvd_add h1 h2
          have heq : r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s = V := by
            calc
              r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s =
                  V * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
              _ = V * 1 := by rw [hbez]
              _ = V := by ring
          rwa [heq] at hsum
        rcases hsY with ⟨q, hq⟩
        rcases hrV with ⟨q', hq'⟩
        have hqq : q = q' := by
          have hmain : r * s * q = r * s * q' := by
            calc
              r * s * q = r * (s * q) := by ring
              _ = r * Y := by rw [← hq]
              _ = s * V := hrY
              _ = s * (r * q') := by rw [hq']
              _ = r * s * q' := by ring
          exact mul_left_cancel₀ (mul_ne_zero hr_ne hs_ne) hmain
        refine ⟨g, q, r, s, ?_, ?_, ?_, ?_⟩
        · calc
            X = r * g := hXeq
            _ = g * r := by ring
        · rw [hq]
          ring
        · calc
            U = s * g := hUeq
            _ = g * s := by ring
        · rw [hq', ← hqq]
          ring
  -- ------------------------------------------------------------------ assembly
  rcases parity a b c d h with hleft | hright
  · rcases hleft with ⟨hac, hbd⟩
    obtain ⟨X, Y, U, V, hXa, hXc, hUb, hUd, hprod⟩ := halves a b c d h hac hbd
    obtain ⟨p, q, r, s, hpr, hqs, hps, hqr⟩ := factor X Y U V hprod
    left
    refine ⟨p, q, r, s, ?_, ?_, ?_, ?_⟩
    · calc
        a = X + Y := hXa.symm
        _ = p * r + q * s := by rw [hpr, hqs]
    · calc
        b = U - V := hUb.symm
        _ = p * s - q * r := by rw [hps, hqr]
    · calc
        c = X - Y := hXc.symm
        _ = p * r - q * s := by rw [hpr, hqs]
    · calc
        d = U + V := hUd.symm
        _ = p * s + q * r := by rw [hps, hqr]
  · rcases hright with ⟨had, hbc⟩
    have h' : a^2 + b^2 = d^2 + c^2 := by nlinarith
    obtain ⟨X, Y, U, V, hXa, hXd, hUb, hUc, hprod⟩ := halves a b d c h' had hbc
    obtain ⟨p, q, r, s, hpr, hqs, hps, hqr⟩ := factor X Y U V hprod
    right
    refine ⟨p, q, r, s, ?_, ?_, ?_, ?_⟩
    · calc
        a = X + Y := hXa.symm
        _ = p * r + q * s := by rw [hpr, hqs]
    · calc
        b = U - V := hUb.symm
        _ = p * s - q * r := by rw [hps, hqr]
    · calc
        d = X - Y := hXd.symm
        _ = p * r - q * s := by rw [hpr, hqs]
    · calc
        c = U + V := hUc.symm
        _ = p * s + q * r := by rw [hps, hqr]
