-- Prove2me | solution 1 for Bernstein.theorem_B_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:54:54.08781+00:00
-- url     : https://prove2.me/submissions/7c9a137b-2ff9-4c64-842c-52380c9372f2

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_group_law
import Theorems.Thm_Bernstein_eq_zero_of_cubic_eq_zero

namespace Bernstein.Montgomery
open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime] {A : ℤ}

lemma natCast_ne_zero_of_lt (hp : 5 ≤ p) (n : ℕ) (hn0 : 0 < n) (hn : n < 5) :
    ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro h
  have := Nat.le_of_dvd hn0 h
  omega

lemma four_ne_zero' (hp : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  exact_mod_cast natCast_ne_zero_of_lt hp 4 (by norm_num) (by norm_num)

lemma four_ne_zero_Fp2 (hp : 5 ≤ p) : (4 : Fp2 p) ≠ 0 := by
  intro h
  apply four_ne_zero' hp
  apply (emb p).injective
  rw [map_ofNat, map_zero]; exact h

lemma curve_eq (u y : Fp2 p) (h : (Ecurve p A).Nonsingular u y) :
    y ^ 2 = u ^ 3 + emb p A * u ^ 2 + u := by
  have := h.1
  rw [Affine.equation_iff] at this
  simp [Ecurve, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map] at this
  rw [map_intCast]
  linear_combination this

lemma frac_eq_none {x z : ZMod p} : frac x z = (none : Option (Fp2 p)) ↔ z = 0 := by
  unfold frac; split_ifs with h <;> simp [h]

lemma frac_eq_some {x z : ZMod p} {u : Fp2 p} :
    frac x z = some u ↔ z ≠ 0 ∧ u = emb p (x / z) := by
  unfold frac; split_ifs with h <;> simp [h, eq_comm]

lemma frac_of_ne {x z : ZMod p} (hz : z ≠ 0) : frac x z = some (emb p (x / z)) := by
  simp [frac, hz]

lemma X_zero : X (0 : Pt p A) = none := rfl

lemma X_some (u y : Fp2 p) (h) : X (.some u y h : Pt p A) = some u := rfl

theorem doubling (hp : 5 ≤ p) (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (x z : ZMod p)
    (hxz : (x, z) ≠ (0, 0)) (Q : Pt p A) (hQ : X Q = frac x z) :
    ((x ^ 2 - z ^ 2) ^ 2, 4 * x * z * (x ^ 2 + (A : ZMod p) * x * z + z ^ 2)) ≠ (0, 0) ∧
      X (2 • Q) = frac ((x ^ 2 - z ^ 2) ^ 2) (4 * x * z * (x ^ 2 + (A : ZMod p) * x * z + z ^ 2)) := by
  obtain ⟨-, -, -, hneg0, -, hnegsome, -, hzero, hinv, hdbl, -⟩ := group_law p hp A hA
  rw [two_nsmul]
  cases Q with
  | zero =>
    have hz : z = 0 := frac_eq_none.mp hQ.symm
    subst hz
    have hx : x ≠ 0 := by intro hx; exact hxz (by simp [hx])
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg Prod.fst h
      simp at this
      exact hx this
    · have e : (Affine.Point.zero : Pt p A) + Affine.Point.zero = 0 := (hzero 0).1
      rw [e]; simp [frac]; rfl
  | some u y h =>
    obtain ⟨hz, hu⟩ := frac_eq_some.mp hQ.symm
    have hy2 := curve_eq u y h
    by_cases hx : x = 0
    · subst hx
      have hu0 : u = 0 := by simp [hu]
      subst hu0
      have hy : y = 0 := by
        have : y ^ 2 = 0 := by rw [hy2]; ring
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hy
      refine ⟨?_, ?_⟩
      · intro h'
        have := congrArg Prod.fst h'
        simp at this
        exact hz this
      · have h1 : (Ecurve p A).Nonsingular 0 (-0) := by simpa using h
        have := hinv 0 0 h h1
        simp only [neg_zero] at this
        rw [this]
        simp [X_zero, frac]
    · have hy : y ≠ 0 := by
        rintro rfl
        apply (eq_zero_of_cubic_eq_zero p hp A hA).2 (x / z) (div_ne_zero hx hz)
        rw [← hu]; exact h.1
      obtain ⟨hx'', h'', hsum⟩ := hdbl u y h hy
      rw [hsum, X_some]
      -- z₂ = 4 y² z⁴ in F_{p²}
      have hz2 : emb p (4 * x * z * (x ^ 2 + (A : ZMod p) * x * z + z ^ 2)) =
          4 * y ^ 2 * emb p z ^ 4 := by
        have hzF : emb p z ≠ 0 := by simpa using hz
        rw [hy2, hu]
        simp only [map_mul, map_add, map_pow, map_div₀, map_ofNat]
        field_simp
      have hz2ne : 4 * x * z * (x ^ 2 + (A : ZMod p) * x * z + z ^ 2) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hz2
        have hzF : emb p z ≠ 0 := by simpa using hz
        have := four_ne_zero_Fp2 (p := p) hp
        have : (4 : Fp2 p) * y ^ 2 * emb p z ^ 4 ≠ 0 := by positivity
        exact this hz2.symm
      refine ⟨fun h0 => hz2ne (congrArg Prod.snd h0), ?_⟩
      rw [frac_of_ne hz2ne]
      congr 1
      rw [hx'', map_div₀, hz2, hu]
      have hzF : emb p z ≠ 0 := by simpa using hz
      simp only [map_mul, map_add, map_pow, map_div₀, map_sub]
      field_simp

theorem theorem_B_1_dev (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (x z : ZMod p) (hxz : (x, z) ≠ (0, 0)) :
    let x₂ := (x ^ 2 - z ^ 2) ^ 2
    let z₂ := 4 * x * z * (x ^ 2 + (A : ZMod p) * x * z + z ^ 2)
    x₂ = (x - z) ^ 2 * (x + z) ^ 2 ∧
    z₂ = ((x + z) ^ 2 - (x - z) ^ 2) *
      ((x + z) ^ 2 + ((A : ZMod p) - 2) / 4 * ((x + z) ^ 2 - (x - z) ^ 2)) ∧
    ∀ Q : Pt p A, X Q = frac x z → (x₂, z₂) ≠ (0, 0) ∧ X (2 • Q) = frac x₂ z₂ := by
  intro x₂ z₂
  have hc : ((A : ZMod p) - 2) / 4 * 4 = (A : ZMod p) - 2 := div_mul_cancel₀ _ (four_ne_zero' hp)
  refine ⟨by ring, by linear_combination (-4 * x ^ 2 * z ^ 2) * hc, ?_⟩
  intro Q hQ
  exact doubling hp hA x z hxz Q hQ

end Bernstein.Montgomery

theorem solution : type_of% @Bernstein.Montgomery.theorem_B_1_dev := @Bernstein.Montgomery.theorem_B_1_dev
