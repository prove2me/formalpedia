-- Prove2me | solution 1 for BitcoinMuSig.toPoint_padd
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T03:45:06.690957+00:00
-- url     : https://prove2.me/submissions/cfe4b34c-07f7-43aa-a71b-9eb33f6f26a7

import Definitions.Def_BitcoinMuSig
import Mathlib

open BitcoinMuSig BitcoinSig BitcoinTaproot

private theorem p_two_le : 2 ≤ p := by decide

private theorem cast_p : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p

private theorem cast_finv (a : ℕ) : ((finv a : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
  rw [finv, powMod_eq, ZMod.natCast_mod]
  push_cast
  by_cases ha : (a : ZMod p) = 0
  · rw [ha, inv_zero, zero_pow]; have := p_two_le; decide
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    have h : p - 2 + 1 = p - 1 := by have := p_two_le; decide
    rw [h]
    exact ZMod.pow_card_sub_one_eq_one ha

private theorem cast_p_sub_mod (b : ℕ) : ((p - b % p : ℕ) : ZMod p) = -(b : ZMod p) := by
  have hb : b % p ≤ p := (Nat.mod_lt _ (by decide)).le
  rw [Nat.cast_sub hb, cast_p, ZMod.natCast_mod, zero_sub]

private theorem cast_add_p_sub (a b : ℕ) (hb : b ≤ p) : ((a + p - b : ℕ) : ZMod p) = a - b := by
  rw [Nat.cast_sub (by omega), Nat.cast_add, cast_p, add_zero]

private theorem cast_add_p_sub_mod (a b : ℕ) : ((a + p - b % p : ℕ) : ZMod p) = a - b := by
  rw [cast_add_p_sub _ _ (Nat.mod_lt _ (by decide)).le, ZMod.natCast_mod]

private theorem W_a₁ : W.a₁ = 0 := rfl

private theorem W_a₂ : W.a₂ = 0 := rfl

private theorem W_a₃ : W.a₃ = 0 := rfl

private theorem W_a₄ : W.a₄ = 0 := rfl

private theorem W_negY (x y : ZMod p) : W.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, W_a₁, W_a₃]

private theorem onCurve_of_nonsingular {x y : ℕ} {X Y : ZMod p} (h : W.Nonsingular X Y)
    (hx : (x : ZMod p) = X) (hy : (y : ZMod p) = Y) : onCurve (x, y) = true :=
  (equation_iff_onCurve x y).mp (hx ▸ hy ▸ h.1)

private theorem toPoint_eq {x y : ℕ} {X Y : ZMod p} (h : W.Nonsingular X Y)
    (hx : (x : ZMod p) = X) (hy : (y : ZMod p) = Y) : toPoint (some (x, y)) = some (.some X Y h) := by
  have hc := onCurve_of_nonsingular h hx hy
  simp only [toPoint, hc, dif_pos]
  subst hx; subst hy; rfl

private theorem toPoint_of_onCurve {x y : ℕ} (h : onCurve (x, y) = true) :
    toPoint (some (x, y)) = some (.some (x : ZMod p) (y : ZMod p) (nonsingular_of_onCurve h)) :=
  toPoint_eq _ rfl rfl

private theorem tp_of_onCurve {x y : ℕ} (h : onCurve (x, y) = true) :
    tp (some (x, y)) = .some (x : ZMod p) (y : ZMod p) (nonsingular_of_onCurve h) := by
  simp [tp, toPoint_of_onCurve h]

private theorem toPoint_of_valid {P : Point} (hP : Valid P) : toPoint P = some (tp P) := by
  rcases P with _ | ⟨x, y⟩
  · rfl
  · rw [tp_of_onCurve (hP x y rfl), toPoint_of_onCurve (hP x y rfl)]

private theorem natCast_eq_iff (a b : ℕ) : a % p = b % p ↔ (a : ZMod p) = b :=
  (ZMod.natCast_eq_natCast_iff' a b p).symm

private theorem natCast_eq_zero_iff' (a : ℕ) : a % p = 0 ↔ (a : ZMod p) = 0 := by
  rw [← ZMod.natCast_mod, ← Nat.cast_zero (R := ZMod p)]
  constructor
  · intro h; rw [h]
  · intro h; rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.zero_mod] at h; exact h

private theorem toPoint_addFormula (x1 y1 x2 l x3 : ℕ) {L : ZMod p} (hl : (l : ZMod p) = L)
    (hx3 : (x3 : ZMod p) = (l : ZMod p) ^ 2 - x1 - x2)
    (h : W.Nonsingular (W.addX (x1 : ZMod p) x2 L) (W.addY (x1 : ZMod p) x2 y1 L)) :
    toPoint (some (x3 % p, (l * ((x1 + p - x3 % p) % p) + (p - y1 % p)) % p)) =
      some (.some _ _ h) := by
  apply toPoint_eq
  · rw [ZMod.natCast_mod, hx3, hl]
    simp [WeierstrassCurve.Affine.addX, W_a₁, W_a₂]
  · simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, cast_add_p_sub_mod, cast_p_sub_mod, hl, hx3]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, W_negY, W_a₁, W_a₂]
    ring

/-- The executable addition is Mathlib's group law on curve points. -/
theorem solution (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    toPoint (padd P Q) = some (tp P + tp Q) := by
  rcases P with _ | ⟨x1, y1⟩ <;> rcases Q with _ | ⟨x2, y2⟩
  · rfl
  · simp only [padd, toPoint_of_valid hQ]; simp [tp, toPoint]
  · simp only [padd, toPoint_of_valid hP]; simp [tp, toPoint]
  have h1 := hP x1 y1 rfl
  have h2 := hQ x2 y2 rfl
  rw [tp_of_onCurve h1, tp_of_onCurve h2]
  simp only [padd]
  split_ifs with hx hy
  · rw [natCast_eq_iff] at hx
    rw [natCast_eq_zero_iff', Nat.cast_add] at hy
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx (by rw [W_negY]; linear_combination hy)]
    rfl
  · rw [natCast_eq_iff] at hx
    rw [natCast_eq_zero_iff', Nat.cast_add] at hy
    have hy' : (y1 : ZMod p) ≠ W.negY x2 y2 := by
      rw [W_negY]; intro h; apply hy; rw [h]; ring
    have hyy : (y1 : ZMod p) = y2 :=
      WeierstrassCurve.Affine.Y_eq_of_Y_ne (nonsingular_of_onCurve h1).1 (nonsingular_of_onCurve h2).1 hx hy'
    rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy']
    have h2y : (2 * (y1 : ZMod p)) ≠ 0 := by
      intro h; apply hy; rw [← hyy]; linear_combination h
    apply toPoint_addFormula
    · simp only [ZMod.natCast_mod, Nat.cast_mul, cast_finv, Nat.cast_ofNat]
      rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy', W_negY]
      simp only [W_a₁, W_a₂, W_a₄]
      field_simp
      ring
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, cast_p_sub_mod, ZMod.natCast_mod, hx]
      ring
  · rw [natCast_eq_iff] at hx
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    have hx' : (x2 : ZMod p) - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    apply toPoint_addFormula
    · simp only [ZMod.natCast_mod, Nat.cast_mul, cast_finv, cast_add_p_sub_mod]
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
      have hx'' : (x1 : ZMod p) - x2 ≠ 0 := sub_ne_zero.mpr hx
      field_simp
      ring
    · simp only [Nat.cast_add, Nat.cast_mul, cast_p_sub_mod, ZMod.natCast_mod]
      ring
