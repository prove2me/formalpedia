-- Prove2me | solution 1 for EqualTwoSquares.parity_alignment
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:07:20.476496+00:00
-- url     : https://prove2.me/submissions/0c0e7983-c6fd-4cb6-91fb-38fc153eb60d

-- Public-mission submission for EqualTwoSquares.parity_alignment.

import Mathlib

theorem solution {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by
  -- Two ways of subtracting parities. Both are read off from witnesses, so no parity
  -- lemma library is needed.
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
  -- A square is 0 or 1 modulo 4 according to the parity of its root.
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
  -- If the four residues rx,ry,rz,rw (each 0 or 1) do not satisfy rx+ry = rz+rw, then
  -- the equation is impossible: subtracting the residues shows 4 divides rz+rw-rx-ry,
  -- which lies strictly between -4 and 4 and is nonzero.
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
