-- Prove2me | solution 1 for BitcoinMuSig.toPoint_pneg
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T03:48:04.151254+00:00
-- url     : https://prove2.me/submissions/228ce4e8-b33b-4465-a8d0-c5498cdfc32f

import Definitions.Def_BitcoinMuSig
import Mathlib
import Theorems.Thm_BitcoinMuSig_tp_padd
import Theorems.Thm_BitcoinMuSig_valid_padd

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

private theorem valid_of_toPoint {P : Point} {T : W.Point} (h : toPoint P = some T) : Valid P := by
  intro x y hP
  subst hP
  by_contra hc
  simp [toPoint, hc] at h

private theorem tp_of_toPoint {P : Point} {T : W.Point} (h : toPoint P = some T) : tp P = T := by
  simp [tp, h]

private theorem pmulAux_spec : ∀ (fuel k : ℕ) (P acc : Point), Valid P → Valid acc → k < 2 ^ fuel →
    Valid (pmulAux fuel k P acc) ∧ tp (pmulAux fuel k P acc) = tp acc + k • tp P := by
  intro fuel
  induction fuel with
  | zero =>
    intro k P acc _ hacc hk
    have : k = 0 := by simpa using hk
    subst this
    simp [pmulAux, hacc]
  | succ f ih =>
    intro k P acc hP hacc hk
    simp only [pmulAux]
    split_ifs with h0 h1
    · subst h0; simp [hacc]
    · have hk' : k / 2 < 2 ^ f := by rw [pow_succ] at hk; omega
      obtain ⟨hv, ht⟩ := ih (k / 2) (padd P P) (padd acc P) (valid_padd _ _ hP hP)
        (valid_padd _ _ hacc hP) hk'
      refine ⟨hv, ?_⟩
      rw [ht, tp_padd _ _ hP hP, tp_padd _ _ hacc hP]
      conv_rhs => rw [← Nat.div_add_mod k 2, h1]
      rw [← two_nsmul, smul_smul, add_smul, one_smul, mul_comm]
      abel
    · have hk' : k / 2 < 2 ^ f := by rw [pow_succ] at hk; omega
      obtain ⟨hv, ht⟩ := ih (k / 2) (padd P P) acc (valid_padd _ _ hP hP) hacc hk'
      refine ⟨hv, ?_⟩
      have h2 : k % 2 = 0 := by omega
      rw [ht, tp_padd _ _ hP hP]
      conv_rhs => rw [← Nat.div_add_mod k 2, h2]
      rw [← two_nsmul, smul_smul, add_zero, mul_comm]

private theorem reduced_padd (P Q : Point) (hP : Reduced P) (hQ : Reduced Q) : Reduced (padd P Q) := by
  have hp : 0 < p := by decide
  rcases P with _ | ⟨x1, y1⟩ <;> rcases Q with _ | ⟨x2, y2⟩
  · exact hQ
  · exact hQ
  · exact hP
  intro x y h
  simp only [padd] at h
  split_ifs at h <;> cases h <;> exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

private theorem reduced_pmulAux : ∀ (fuel k : ℕ) (P acc : Point), Reduced P → Reduced acc →
    Reduced (pmulAux fuel k P acc) := by
  intro fuel
  induction fuel with
  | zero => intro k P acc _ hacc; exact hacc
  | succ f ih =>
    intro k P acc hP hacc
    simp only [pmulAux]
    split_ifs
    · exact hacc
    · exact ih _ _ _ (reduced_padd _ _ hP hP) (reduced_padd _ _ hacc hP)
    · exact ih _ _ _ (reduced_padd _ _ hP hP) hacc

private theorem reduced_pmul (k : ℕ) (P : Point) (hP : Reduced P) : Reduced (pmul k P) :=
  reduced_pmulAux _ _ _ _ hP (by intro x y h; cases h)

private theorem n_lt_256 : n < 2 ^ 256 := by unfold n; norm_num

set_option exponentiation.threshold 300 in

private theorem n_lt_257 : n < 2 ^ 257 := lt_trans n_lt_256 (Nat.pow_lt_pow_succ (by norm_num))

private theorem n_pos : 0 < n := by unfold n; norm_num

private theorem one_lt_n : 1 < n := by unfold n; norm_num

set_option maxRecDepth 100000 in

private theorem pmul_n_G : pmul n G = none := by decide +kernel

private theorem beVal_append_single (l : BitcoinSer.Bytes) (a : BitcoinSer.Byte) :
    beVal (l ++ [a]) = beVal l * 256 + a.toNat := by
  simp [beVal, List.foldl_append]

private theorem beVal_reverse (l : BitcoinSer.Bytes) : beVal l.reverse = BitcoinSer.leVal l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, beVal_append_single, ih, BitcoinSer.leVal]
    ring

private theorem leVal_leBytes : ∀ (k x : ℕ), BitcoinSer.leVal (BitcoinSer.leBytes k x) = x % 256 ^ k := by
  intro k
  induction k with
  | zero => intro x; simp [BitcoinSer.leBytes, BitcoinSer.leVal, Nat.mod_one]
  | succ k ih =>
    intro x
    rw [BitcoinSer.leBytes, BitcoinSer.leVal, ih, pow_succ, mul_comm (256 ^ k) 256, Nat.mod_mul]
    simp [BitVec.toNat_ofNat]

private theorem length_leBytes : ∀ (k x : ℕ), (BitcoinSer.leBytes k x).length = k := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; simp [BitcoinSer.leBytes, ih]

private theorem beVal_be32 (x : ℕ) (hx : x < 2 ^ 256) : beVal (be32 x) = x := by
  rw [be32, BitcoinSer.beBytes, beVal_reverse, leVal_leBytes, Nat.mod_eq_of_lt]
  calc x < 2 ^ 256 := hx
    _ = 256 ^ 32 := by norm_num

private theorem length_be32 (x : ℕ) : (be32 x).length = 32 := by
  rw [be32, BitcoinSer.beBytes, List.length_reverse, length_leBytes]

private theorem p_lt_256 : p < 2 ^ 256 := by unfold p; norm_num

private theorem p_odd : p % 2 = 1 := by decide

private theorem natCast_inj_of_lt {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = b) : a = b := by
  rw [← natCast_eq_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h; exact h

/-- `pneg ↦ -`. -/
theorem solution (P : Point) (hP : Valid P) : toPoint (pneg P) = some (-tp P) := by
  rcases P with _ | ⟨x, y⟩
  · rfl
  · have h := hP x y rfl
    rw [tp_of_onCurve h, WeierstrassCurve.Affine.Point.neg_some]
    apply toPoint_eq
    · rfl
    · rw [ZMod.natCast_mod, cast_p_sub_mod, W_negY]
