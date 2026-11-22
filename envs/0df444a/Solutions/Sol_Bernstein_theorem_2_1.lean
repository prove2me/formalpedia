-- Prove2me | solution 1 for Bernstein.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:53:24.318134+00:00
-- url     : https://prove2.me/submissions/06ec441e-2137-42da-ad2b-b24c033b0ad5

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_addSubgroups
import Theorems.Thm_Bernstein_group_law
import Theorems.Thm_Bernstein_eq_zero_of_cubic_eq_zero

namespace Bernstein.Goal

open WeierstrassCurve

/-- Every element of `F_p` is a square in `F_{p²}` (`p` odd). -/
theorem exists_sq_eq_emb (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ZMod p) :
    ∃ y : Fp2 p, y ^ 2 = emb p a := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hchar : ringChar (Fp2 p) ≠ 2 := by
    rw [ringChar.eq (Fp2 p) p]; exact hp2
  have hne : emb p a ≠ 0 := by simpa using ha
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  have : Fintype (Fp2 p) := Fintype.ofFinite _
  have hcard : Fintype.card (Fp2 p) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 (by norm_num)
  have hk : Fintype.card (Fp2 p) / 2 = (p - 1) * (m + 1) := by
    rw [hcard, hm]
    have h1 : (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 := by ring
    have h2 : 2 * m + 1 - 1 = 2 * m := by omega
    rw [h1, h2]
    generalize 2 * m * (m + 1) = X
    omega
  have hsq : IsSquare (emb p a) := by
    rw [FiniteField.isSquare_iff hchar hne, hk, pow_mul, ← map_pow,
      ZMod.pow_card_sub_one_eq_one ha]
    simp
  obtain ⟨r, hr⟩ := hsq
  exact ⟨r, by rw [hr]; ring⟩

theorem equation_iff' (p : ℕ) [Fact p.Prime] (A : ℤ) (x y : Fp2 p) :
    (Ecurve p A).Equation x y ↔ y ^ 2 = x ^ 3 + emb p A * x ^ 2 + x := by
  rw [Affine.equation_iff]
  simp [Ecurve, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem X0_neg (p : ℕ) [Fact p.Prime] (A : ℤ) (P : Pt p A) : X0 (-P) = X0 P := by
  cases P with
  | zero => rfl
  | some h => rw [Affine.Point.neg_some]; rfl

theorem theorem_2_1_dev (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (n : ℤ) (q : ZMod p) :
    ∃! s : ZMod p, ∀ Q : Pt p A, X0 Q = emb p q → X0 (n • Q) = emb p s := by
  obtain ⟨⟨H1, hH1⟩, ⟨Hf, hHf⟩, hHt⟩ := Bernstein.addSubgroups p hp A hA
  have hnonsing := (Bernstein.group_law p hp A hA).1
  have hcub := (Bernstein.eq_zero_of_cubic_eq_zero p hp A hA).1
  have hp2 : p ≠ 2 := by omega
  suffices h : ∃ s : ZMod p, (∀ Q : Pt p A, X0 Q = emb p q → X0 (n • Q) = emb p s) ∧
      ∃ Q0 : Pt p A, X0 Q0 = emb p q by
    obtain ⟨s, hs, Q0, hQ0⟩ := h
    refine ⟨s, hs, fun s' hs' => (emb p).injective ?_⟩
    rw [← hs' Q0 hQ0, hs Q0 hQ0]
  -- the points over `q`
  have hfib : ∀ Q : Pt p A, X0 Q = emb p q →
      (Q = 0 ∧ q = 0) ∨ ∃ (y : Fp2 p) (h : (Ecurve p A).Nonsingular (emb p q) y),
        Q = .some (emb p q) y h ∧ y ^ 2 = emb p (q ^ 3 + (A : ZMod p) * q ^ 2 + q) := by
    intro Q hQ
    cases Q with
    | zero =>
      left; refine ⟨rfl, ?_⟩
      have : emb p q = 0 := hQ.symm
      simpa using this
    | @some x y h =>
      right
      have hx : x = emb p q := hQ
      subst hx
      refine ⟨y, h, rfl, ?_⟩
      have := (equation_iff' p A _ _).1 h.1
      rw [this]; simp
  by_cases hα : q ^ 3 + (A : ZMod p) * q ^ 2 + q = 0
  · -- `α = 0`: `q = 0` and the points lie in `{∞, (0, 0)}`
    have hq : q = 0 := hcub q hα
    refine ⟨0, fun Q hQ => ?_, 0, by simp [hq]; rfl⟩
    have hQmem : Q ∈ H1 := by
      rw [← SetLike.mem_coe, hH1]
      rcases hfib Q hQ with ⟨rfl, -⟩ | ⟨y, h, rfl, hy⟩
      · exact Or.inl rfl
      · rw [hα, map_zero, sq_eq_zero_iff] at hy
        subst hy
        simp only [hq, map_zero] at h ⊢
        exact Or.inr ⟨h, rfl⟩
    have hn : n • Q ∈ (H1 : Set (Pt p A)) := H1.zsmul_mem hQmem n
    rw [hH1] at hn
    rcases hn with hn | ⟨h, hn⟩
    · rw [hn]; simp; rfl
    · rw [hn]; simp; rfl
  · -- `α ≠ 0`: the points over `q` are `±Q0`
    obtain ⟨y0, hy0⟩ := exists_sq_eq_emb p hp2 (q ^ 3 + (A : ZMod p) * q ^ 2 + q)
    have h0 : (Ecurve p A).Nonsingular (emb p q) y0 :=
      hnonsing _ _ (by rw [hy0]; simp)
    set Q0 : Pt p A := .some (emb p q) y0 h0 with hQ0def
    have hpm : ∀ Q : Pt p A, X0 Q = emb p q → Q = Q0 ∨ Q = -Q0 := by
      intro Q hQ
      rcases hfib Q hQ with ⟨-, hq⟩ | ⟨y, h, rfl, hy⟩
      · exact absurd (by rw [hq]; ring) hα
      · rw [← hy0, sq_eq_sq_iff_eq_or_eq_neg] at hy
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · right
          rw [hQ0def, Affine.Point.neg_some]
          simp [Affine.negY, Ecurve, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
          rfl
    have hX0 : ∀ Q : Pt p A, X0 Q = emb p q → X0 (n • Q) = X0 (n • Q0) := by
      intro Q hQ
      rcases hpm Q hQ with rfl | rfl
      · rfl
      · rw [zsmul_neg, X0_neg]
    suffices hs : ∃ s : ZMod p, X0 (n • Q0) = emb p s by
      obtain ⟨s, hs⟩ := hs
      exact ⟨s, fun Q hQ => (hX0 Q hQ).trans hs, Q0, rfl⟩
    by_cases hsq : IsSquare (q ^ 3 + (A : ZMod p) * q ^ 2 + q)
    · -- `α = r²`: `Q0` is an `F_p`-point
      obtain ⟨r, hr⟩ := hsq
      have hmem : Q0 ∈ Hf := by
        rw [← SetLike.mem_coe, hHf]
        right
        rw [hr, map_mul, ← sq, sq_eq_sq_iff_eq_or_eq_neg] at hy0
        rcases hy0 with hy | hy
        · exact ⟨q, r, by rw [← hy]; exact h0, by rw [hQ0def]; congr⟩
        · rw [← map_neg] at hy
          exact ⟨q, -r, by rw [← hy]; exact h0, by rw [hQ0def]; congr⟩
      have hn : n • Q0 ∈ (Hf : Set (Pt p A)) := Hf.zsmul_mem hmem n
      rw [hHf] at hn
      rcases hn with hn | ⟨x, y, h, hn⟩
      · exact ⟨0, by rw [hn]; simp; rfl⟩
      · exact ⟨x, by rw [hn]; rfl⟩
    · -- `α` a non-square: `Q0` lies in the twist subgroup
      set d := ((A : ZMod p) ^ 2 - 4).val with hd
      have hdne : ((A : ZMod p) ^ 2 - 4) ≠ 0 := fun h => hA (by rw [h]; exact ⟨0, by simp⟩)
      have hdmem : d ∈ {d : ℕ | 1 ≤ d ∧ d < p ∧ ¬ IsSquare (d : ZMod p)} := by
        refine ⟨?_, ZMod.val_lt _, ?_⟩
        · rw [Nat.one_le_iff_ne_zero, hd]; exact (ZMod.val_ne_zero _).2 hdne
        · rw [hd, ZMod.natCast_zmod_val]; exact hA
      have hδ : ¬ IsSquare ((delta p : ℕ) : ZMod p) := (Nat.sInf_mem ⟨d, hdmem⟩).2.2
      have hδ0 : ((delta p : ℕ) : ZMod p) ≠ 0 := fun h => hδ (by rw [h]; exact ⟨0, by simp⟩)
      have hprod : IsSquare ((q ^ 3 + (A : ZMod p) * q ^ 2 + q) * ((delta p : ℕ) : ZMod p)) := by
        rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hα hδ0), map_mul,
          quadraticChar_neg_one_iff_not_isSquare.2 hsq,
          quadraticChar_neg_one_iff_not_isSquare.2 hδ]
        norm_num
      obtain ⟨t, ht⟩ := hprod
      obtain ⟨s0, hs0⟩ := exists_sq_eq_emb p hp2 ((delta p : ℕ) : ZMod p)
      obtain ⟨H, hH⟩ := hHt s0 hs0
      set c := t / ((delta p : ℕ) : ZMod p) with hc
      have hαc : q ^ 3 + (A : ZMod p) * q ^ 2 + q = ((delta p : ℕ) : ZMod p) * c ^ 2 := by
        rw [hc]; field_simp; linear_combination ht
      have hmem : Q0 ∈ H := by
        rw [← SetLike.mem_coe, hH]
        right
        have hy' : y0 ^ 2 = (s0 * emb p c) ^ 2 := by
          rw [hy0, hαc, mul_pow, hs0]; simp
        rw [sq_eq_sq_iff_eq_or_eq_neg] at hy'
        rcases hy' with hy | hy
        · exact ⟨q, c, by rw [← hy]; exact h0, by rw [hQ0def]; congr⟩
        · have hy2 : y0 = s0 * emb p (-c) := by rw [hy, map_neg]; ring
          exact ⟨q, -c, by rw [← hy2]; exact h0, by rw [hQ0def]; congr⟩
      have hn : n • Q0 ∈ (H : Set (Pt p A)) := H.zsmul_mem hmem n
      rw [hH] at hn
      rcases hn with hn | ⟨x, y, h, hn⟩
      · exact ⟨0, by rw [hn]; simp; rfl⟩
      · exact ⟨x, by rw [hn]; rfl⟩

end Bernstein.Goal

theorem solution : type_of% @Bernstein.Goal.theorem_2_1_dev := @Bernstein.Goal.theorem_2_1_dev
