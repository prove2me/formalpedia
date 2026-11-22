-- Prove2me | solution 1 for Bernstein.ladder_eq_curve25519
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:59:38.567904+00:00
-- url     : https://prove2.me/submissions/560f511e-1a29-43e3-97e2-d6cf6f594612

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_ladderIter_spec
import Theorems.Thm_Bernstein_curve25519_spec

set_option autoImplicit false

namespace Bernstein.LadderEq

theorem secretKeys_lt {n : ℕ} (hn : n ∈ secretKeys) : n / 2 ^ 255 = 0 := by
  obtain ⟨i, hi, rfl⟩ := hn
  norm_num at hi ⊢; omega

theorem secretKeys_even {n : ℕ} (hn : n ∈ secretKeys) : ∃ m : ℕ, n = m + m := by
  obtain ⟨i, hi, rfl⟩ := hn
  exact ⟨2 ^ 253 + 4 * i, by ring⟩

theorem emb_injective [Fact p25519.Prime] : Function.Injective (emb p25519) :=
  (emb p25519).injective

theorem p_sub_two_ne_zero : p25519 - 2 ≠ 0 := by unfold p25519; norm_num

/-- Fermat: `x · z^(p−2) = x / z` in `F_p`. -/
theorem mul_pow_sub_two [Fact p25519.Prime] (x z : ZMod p25519) (hz : z ≠ 0) :
    x * z ^ (p25519 - 2) = x / z := by
  rw [eq_div_iff hz, mul_assoc, ← pow_succ]
  have : p25519 - 2 + 1 = p25519 - 1 := by unfold p25519; norm_num
  rw [this, ZMod.pow_card_sub_one_eq_one hz, mul_one]

/-- A point with `X₀(Q) = q ≠ 0` is affine with `X(Q) = q`. -/
theorem X_of_X0 [Fact p25519.Prime] (q : ZMod p25519) (hq : q ≠ 0) (Q : Pt p25519 A25519)
    (hQ : X0 Q = emb p25519 q) : X Q = some (emb p25519 q) := by
  cases Q with
  | zero =>
    simp only [X0] at hQ
    exact absurd (emb_injective (hQ.symm.trans (map_zero _).symm)) hq
  | some x y h => simp only [X0] at hQ; simp [X, hQ]

/-- The ladder for `q ≠ 0`: `ladderIter_spec` from `X(0) = 1/0`, `X(Q) = q/1`. -/
theorem part2 [Fact p25519.Prime] (n : ℕ) (hn : n ∈ secretKeys) (q : ZMod p25519)
    (Q : Pt p25519 A25519) (hq : q ≠ 0) (hQ : X0 Q = emb p25519 q) :
    let st := ladderIter (121665 : ZMod p25519) q n 255 (1, 0, q, 1)
    (st.1, st.2.1) ≠ (0, 0) ∧ frac st.1 st.2.1 = X ((n : ℤ) • Q) := by
  have hX := X_of_X0 q hq Q hQ
  have h0 := secretKeys_lt hn
  have S := ladderIter_spec q hq Q hX n 255 1 0 q 1 (by simp) (by simp)
    (by rw [h0]; simp [frac, X]) (by rw [h0]; simp [frac, hX])
  exact ⟨S.1, S.2.2.1⟩

/-- With `q = 0` every computed denominator is `0`. -/
theorem step_zero (b : Bool) (st : ZMod p25519 × ZMod p25519 × ZMod p25519 × ZMod p25519)
    (h1 : st.1 * st.2.1 = 0) (h2 : st.2.2.1 * st.2.2.2 = 0) :
    (ladderStep (121665 : ZMod p25519) 0 b st).2.1 = 0 ∧
      (ladderStep (121665 : ZMod p25519) 0 b st).2.2.2 = 0 := by
  obtain ⟨x, z, x', z'⟩ := st
  have e : ∀ u v : ZMod p25519, (u + v) ^ 2 - (u - v) ^ 2 = 4 * (u * v) := fun u v => by ring
  cases b <;> simp [ladderStep, e, h1, h2]

theorem iter_zero (n : ℕ) : ∀ (k : ℕ) (st : ZMod p25519 × ZMod p25519 × ZMod p25519 × ZMod p25519),
    st.1 * st.2.1 = 0 → st.2.2.1 * st.2.2.2 = 0 → 1 ≤ k →
    (ladderIter (121665 : ZMod p25519) 0 n k st).2.1 = 0 ∧
      (ladderIter (121665 : ZMod p25519) 0 n k st).2.2.2 = 0
  | 0, _, _, _, hk => absurd hk (by norm_num)
  | k + 1, st, h1, h2, _ => by
    have hs := step_zero (n.testBit k) st h1 h2
    simp only [ladderIter]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [ladderIter] using hs
    · exact iter_zero n k _ (by rw [hs.1, mul_zero]) (by rw [hs.2, mul_zero]) hk

theorem part3 (n : ℕ) : ∀ k : ℕ, 1 ≤ k →
    (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.1 = 0 ∧
    (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.2.2 = 0 :=
  fun k hk => iter_zero n k _ (by simp) (by simp) hk

/-- If `X₀(Q) = 0` then `2Q = 0`. -/
theorem two_torsion [Fact p25519.Prime] (Q : Pt p25519 A25519) (hQ : X0 Q = 0) : Q + Q = 0 := by
  cases Q with
  | zero => exact add_zero (0 : Pt p25519 A25519)
  | some x y h =>
    change x = 0 at hQ
    subst hQ
    have hy : y = 0 := by
      have he := h.1
      rw [WeierstrassCurve.Affine.equation_iff] at he
      simpa [curve] using he
    subst hy
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by simp [curve])

theorem part1 [Fact p25519.Prime] (n : ℕ) (hn : n ∈ secretKeys) (q : ZMod p25519)
    (Q : Pt p25519 A25519) (hQ : X0 Q = emb p25519 q) :
    X0 ((n : ℤ) • Q) = emb p25519 (ladder n q) := by
  by_cases hq : q = 0
  · subst hq
    have hz := (part3 n 255 (by norm_num)).1
    have hl : ladder n 0 = 0 := by
      simp only [ladder, hz, zero_pow p_sub_two_ne_zero, mul_zero]
    rw [hl, map_zero]
    obtain ⟨m, rfl⟩ := secretKeys_even hn
    rw [map_zero] at hQ
    have h2 := two_torsion Q hQ
    have : (((m + m : ℕ) : ℤ)) • Q = (m : ℤ) • (Q + Q) := by
      push_cast; rw [smul_add, add_smul]
    rw [this, h2, smul_zero]; rfl
  · obtain ⟨hnd, hfr⟩ := part2 n hn q Q hq hQ
    simp only [ladder]
    generalize ladderIter (121665 : ZMod p25519) q n 255 (1, 0, q, 1) = st at hnd hfr ⊢
    by_cases hz : st.2.1 = 0
    · rw [hz, zero_pow p_sub_two_ne_zero, mul_zero, map_zero]
      have : frac st.1 st.2.1 = none := by simp [frac, hz]
      rw [this] at hfr
      generalize (n : ℤ) • Q = R at hfr ⊢
      cases R with
      | zero => rfl
      | some x y h => simp [X] at hfr
    · rw [mul_pow_sub_two _ _ hz]
      have : frac st.1 st.2.1 = some (emb p25519 (st.1 / st.2.1)) := by simp [frac, hz]
      rw [this] at hfr
      generalize (n : ℤ) • Q = R at hfr ⊢
      cases R with
      | zero => simp [X] at hfr
      | some x y h => simp only [X, Option.some.injEq] at hfr; simp [X0, hfr]

theorem ladder_eq_curve25519_dev [Fact p25519.Prime] (n : ℕ) (hn : n ∈ secretKeys) :
    (∀ (q : ZMod p25519) (Q : Pt p25519 A25519), X0 Q = emb p25519 q →
      X0 ((n : ℤ) • Q) = emb p25519 (ladder n q)) ∧
    (∀ (q : ZMod p25519) (Q : Pt p25519 A25519), q ≠ 0 → X0 Q = emb p25519 q →
      let st := ladderIter (121665 : ZMod p25519) q n 255 (1, 0, q, 1)
      (st.1, st.2.1) ≠ (0, 0) ∧ frac st.1 st.2.1 = X ((n : ℤ) • Q)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.1 = 0 ∧
      (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.2.2 = 0) ∧
    (∀ q : ℕ, q < 2 ^ 256 → curve25519 n q = (ladder n (q : ZMod p25519)).val) := by
  refine ⟨part1 n hn, fun q Q hq hQ => part2 n hn q Q hq hQ, part3 n, fun q hq => ?_⟩
  obtain ⟨hu, hle, hprop, -⟩ := (curve25519_spec).2.2.2.1 n q hn hq
  have hlt : (ladder n (q : ZMod p25519)).val < 2 ^ 255 - 19 := ZMod.val_lt _
  refine hu.unique ⟨hle, hprop⟩ ⟨by norm_num at hlt ⊢; omega, fun Q hQ => ?_⟩
  rw [ZMod.natCast_zmod_val]
  exact part1 n hn _ Q hQ

end Bernstein.LadderEq

open Bernstein Bernstein.LadderEq in
theorem solution [Fact p25519.Prime] (n : ℕ) (hn : n ∈ secretKeys) :
    (∀ (q : ZMod p25519) (Q : Pt p25519 A25519), X0 Q = emb p25519 q →
      X0 ((n : ℤ) • Q) = emb p25519 (ladder n q)) ∧
    (∀ (q : ZMod p25519) (Q : Pt p25519 A25519), q ≠ 0 → X0 Q = emb p25519 q →
      let st := ladderIter (121665 : ZMod p25519) q n 255 (1, 0, q, 1)
      (st.1, st.2.1) ≠ (0, 0) ∧ frac st.1 st.2.1 = X ((n : ℤ) • Q)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.1 = 0 ∧
      (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.2.2 = 0) ∧
    (∀ q : ℕ, q < 2 ^ 256 → curve25519 n q = (ladder n (q : ZMod p25519)).val) :=
  ladder_eq_curve25519_dev n hn
