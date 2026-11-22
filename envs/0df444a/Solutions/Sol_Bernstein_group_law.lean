-- Prove2me | solution 1 for Bernstein.group_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:49:58.057709+00:00
-- url     : https://prove2.me/submissions/f53c8576-b58c-46ca-acaa-609d76892ee8

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein.GroupLawDev

open WeierstrassCurve WeierstrassCurve.Affine

variable {p : ℕ} [Fact p.Prime] {A : ℤ}

lemma Ea₁ : (Ecurve p A).a₁ = 0 := by
  simp [Ecurve, curve]

lemma Ea₂ : (Ecurve p A).a₂ = emb p (A : ZMod p) := by
  simp [Ecurve, curve]

lemma Ea₃ : (Ecurve p A).a₃ = 0 := by
  simp [Ecurve, curve]

lemma Ea₄ : (Ecurve p A).a₄ = 1 := by
  simp [Ecurve, curve]

lemma Ea₆ : (Ecurve p A).a₆ = 0 := by
  simp [Ecurve, curve]

lemma two_ne_zero' (hp : 5 ≤ p) : (2 : Fp2 p) ≠ 0 := by
  have : CharP (Fp2 p) p := inferInstance
  intro h
  have h2 : ((2 : ℕ) : Fp2 p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (Fp2 p) p] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

lemma negY_eq (x y : Fp2 p) : (Ecurve p A).negY x y = -y := by
  simp [Affine.negY, Ecurve, curve]

lemma equation_iff (x y : Fp2 p) :
    (Ecurve p A).Equation x y ↔ y ^ 2 = x ^ 3 + emb p (A : ZMod p) * x ^ 2 + x := by
  rw [Affine.equation_iff, Ea₁, Ea₂, Ea₃, Ea₄, Ea₆]
  constructor <;> intro h <;> linear_combination h

lemma nonsingular_of_eq (hp : 5 ≤ p) (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4))
    (x y : Fp2 p) (h : y ^ 2 = x ^ 3 + emb p (A : ZMod p) * x ^ 2 + x) :
    (Ecurve p A).Nonsingular x y := by
  rw [Affine.nonsingular_iff', equation_iff, Ea₁, Ea₂, Ea₃, Ea₄]
  refine ⟨h, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have h2' : y = 0 := by
    have : 2 * y = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (two_ne_zero' hp)
    · exact h
  subst h2'
  set a := emb p (A : ZMod p)
  -- x (x^2 + a x + 1) = 0 and 3x^2 + 2 a x + 1 = 0
  have hd : 3 * x ^ 2 + 2 * a * x + 1 = 0 := by linear_combination -h1
  by_cases hx : x = 0
  · subst hx; simp at hd
  · have hq : x ^ 2 + a * x + 1 = 0 := by
      have : x * (x ^ 2 + a * x + 1) = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left hx
    have hx2 : 2 * x + a = 0 := by
      have : x * (2 * x + a) = 0 := by linear_combination hd - hq
      exact (mul_eq_zero.mp this).resolve_left hx
    have ha4 : a ^ 2 - 4 = 0 := by linear_combination (-(4 : Fp2 p)) * hq + (2 * x + a) * hx2
    apply hA
    have : emb p ((A : ZMod p) ^ 2 - 4) = 0 := by
      rw [map_sub, map_pow, map_ofNat]; exact ha4
    rw [(injective_iff_map_eq_zero _).mp (emb p).injective _ this]
    exact ⟨0, by ring⟩

lemma some_eq {x y x' y' : Fp2 p} {h : (Ecurve p A).Nonsingular x y} (hx : x = x') (hy : y = y') :
    ∃ h' : (Ecurve p A).Nonsingular x' y', (Affine.Point.some x y h : Pt p A) = .some x' y' h' := by
  subst hx; subst hy; exact ⟨h, rfl⟩

lemma addX_eq (x₁ x₂ l : Fp2 p) :
    (Ecurve p A).addX x₁ x₂ l = l ^ 2 - emb p (A : ZMod p) - x₁ - x₂ := by
  simp only [Affine.addX, Ea₁, Ea₂]; ring

lemma addY_eq (x₁ x₂ y₁ l : Fp2 p) :
    (Ecurve p A).addY x₁ x₂ y₁ l = l * (x₁ - (Ecurve p A).addX x₁ x₂ l) - y₁ := by
  simp only [Affine.addY, Affine.negAddY, negY_eq]; ring

theorem group_law_dev (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    (∀ x y : Fp2 p, y ^ 2 = x ^ 3 + emb p A * x ^ 2 + x → (Ecurve p A).Nonsingular x y) ∧
    (∀ P Q R : Pt p A, P + Q + R = P + (Q + R)) ∧
    (∀ P Q : Pt p A, P + Q = Q + P) ∧
    (∀ Q : Pt p A, Q + -Q = 0) ∧
    -(0 : Pt p A) = 0 ∧
    (∀ (x y : Fp2 p) (h : (Ecurve p A).Nonsingular x y),
      ∃ h₁ : (Ecurve p A).Nonsingular x (-y), -(.some x y h : Pt p A) = .some x (-y) h₁) ∧
    (0 : Pt p A) + 0 = 0 ∧
    (∀ Q : Pt p A, 0 + Q = Q ∧ Q + 0 = Q) ∧
    (∀ (x y : Fp2 p) (h : (Ecurve p A).Nonsingular x y)
      (h₁ : (Ecurve p A).Nonsingular x (-y)),
      (.some x y h : Pt p A) + .some x (-y) h₁ = 0) ∧
    (∀ (x y : Fp2 p) (h : (Ecurve p A).Nonsingular x y), y ≠ 0 →
      let l := (3 * x ^ 2 + 2 * emb p A * x + 1) / (2 * y)
      let x'' := l ^ 2 - emb p A - 2 * x
      x'' = (x ^ 2 - 1) ^ 2 / (4 * y ^ 2) ∧
      ∃ h'' : (Ecurve p A).Nonsingular x'' (l * (x - x'') - y),
        (.some x y h : Pt p A) + .some x y h = .some x'' (l * (x - x'') - y) h'') ∧
    (∀ (x y x' y' : Fp2 p) (h : (Ecurve p A).Nonsingular x y)
      (h' : (Ecurve p A).Nonsingular x' y'), x' ≠ x →
      let l := (y' - y) / (x' - x)
      let x'' := l ^ 2 - emb p A - x - x'
      ∃ h'' : (Ecurve p A).Nonsingular x'' (l * (x - x'') - y),
        (.some x y h : Pt p A) + .some x' y' h' = .some x'' (l * (x - x'') - y) h'') := by
  have h2 := two_ne_zero' (p := p) hp
  refine ⟨fun x y h => nonsingular_of_eq hp hA x y h, add_assoc, add_comm, add_neg_cancel,
    neg_zero, ?_, add_zero 0, fun Q => ⟨zero_add Q, add_zero Q⟩, ?_, ?_, ?_⟩
  · intro x y h
    rw [Affine.Point.neg_some]
    exact some_eq rfl (negY_eq x y)
  · intro x y h h₁
    exact Affine.Point.add_of_Y_eq rfl (by rw [negY_eq, neg_neg])
  · intro x y h hy
    dsimp only
    have heq := (equation_iff x y).mp h.1
    have hy' : y ≠ (Ecurve p A).negY x y := by
      rw [negY_eq]; intro hc
      have : 2 * y = 0 := by linear_combination hc
      exact hy ((mul_eq_zero.mp this).resolve_left h2)
    have hsl : (Ecurve p A).slope x x y y = (3 * x ^ 2 + 2 * emb p A * x + 1) / (2 * y) := by
      rw [Affine.slope_of_Y_ne rfl hy', Ea₁, Ea₂, Ea₄, negY_eq]
      congr 1 <;> ring
    set l := (3 * x ^ 2 + 2 * emb p A * x + 1) / (2 * y) with hl
    refine ⟨?_, ?_⟩
    · have h2y : 2 * y ≠ 0 := mul_ne_zero h2 hy
      have hl2 : l * (2 * y) = 3 * x ^ 2 + 2 * emb p A * x + 1 := by
        rw [hl]; field_simp
      have h4 : (4 : Fp2 p) ≠ 0 := by
        have := mul_ne_zero h2 h2
        rwa [show (2 : Fp2 p) * 2 = 4 by norm_num] at this
      rw [eq_div_iff (mul_ne_zero h4 (pow_ne_zero 2 hy))]
      linear_combination (l * (2 * y) + (3 * x ^ 2 + 2 * emb p A * x + 1)) * hl2
        + (-4 * (emb p A + 2 * x)) * heq
    · rw [Affine.Point.add_self_of_Y_ne hy']
      exact some_eq (by rw [addX_eq, hsl]; ring) (by rw [addY_eq, addX_eq, hsl]; ring)
  · intro x y x' y' h h' hx
    dsimp only
    have hx' : x ≠ x' := fun e => hx e.symm
    have hsl : (Ecurve p A).slope x x' y y' = (y' - y) / (x' - x) := by
      rw [Affine.slope_of_X_ne hx', ← neg_div_neg_eq, neg_sub, neg_sub]
    rw [Affine.Point.add_of_X_ne hx']
    exact some_eq (by rw [addX_eq, hsl]) (by rw [addY_eq, addX_eq, hsl])

end Bernstein.GroupLawDev

theorem solution : type_of% @Bernstein.GroupLawDev.group_law_dev := @Bernstein.GroupLawDev.group_law_dev
