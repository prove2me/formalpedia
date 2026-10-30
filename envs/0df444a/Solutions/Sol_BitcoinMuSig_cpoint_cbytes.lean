-- Prove2me | solution 1 for BitcoinMuSig.cpoint_cbytes
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T03:50:27.713489+00:00
-- url     : https://prove2.me/submissions/6aafc261-0052-4633-a687-2cb18863ee39

import Definitions.Def_BitcoinMuSig
import Mathlib
import Theorems.Thm_BitcoinMuSig_toPoint_pneg
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

private theorem valid_pneg (P : Point) (hP : Valid P) : Valid (pneg P) :=
  valid_of_toPoint (toPoint_pneg P hP)

private theorem tp_pneg (P : Point) (hP : Valid P) : tp (pneg P) = -tp P :=
  tp_of_toPoint (toPoint_pneg P hP)

private theorem reduced_pneg (P : Point) (hP : Reduced P) : Reduced (pneg P) := by
  rcases P with _ | ⟨x, y⟩
  · exact hP
  · intro a b h
    simp only [pneg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(hP x y rfl).1, Nat.mod_lt _ (by decide)⟩

private theorem sqrt_spec (x y : ℕ) (h : onCurve (x, y) = true) :
    let r := powMod (x * x * x + 7) ((p + 1) / 4) p
    r * r % p = (x * x * x + 7) % p ∧ ((r : ZMod p) = y ∨ (r : ZMod p) = -y) := by
  intro r
  have he : ((y * y : ℕ) : ZMod p) = ((x * x * x + 7 : ℕ) : ZMod p) := by
    rw [← natCast_eq_iff]; simpa [onCurve] using h
  have hr : (r : ZMod p) = ((y : ZMod p) ^ 2) ^ ((p + 1) / 4) := by
    simp only [r, powMod_eq, ZMod.natCast_mod, Nat.cast_pow]
    rw [← he]; push_cast; ring
  have hsq : (r : ZMod p) * r = y * y := by
    rw [hr, ← pow_two, ← pow_mul, ← pow_mul]
    have h4 : 2 * ((p + 1) / 4 * 2) = p + 1 := by decide
    rw [h4, pow_succ, ZMod.pow_card]
  refine ⟨?_, ?_⟩
  · rw [natCast_eq_iff]; push_cast; rw [hsq]; exact_mod_cast he
  · have : ((r : ZMod p) - y) * ((r : ZMod p) + y) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1

private theorem liftXParity_of_onCurve (x y : ℕ) (hy : y < p) (h : onCurve (x, y) = true) :
    liftXParity x (decide (y % 2 = 1)) = some (x, y) := by
  obtain ⟨h1, h2⟩ := sqrt_spec x y h
  simp only [liftXParity]
  rw [if_pos h1]
  set r := powMod (x * x * x + 7) ((p + 1) / 4) p with hrdef
  have hrp : r < p := by rw [hrdef, powMod_eq]; exact Nat.mod_lt _ (by decide)
  simp only [Option.some.injEq, Prod.mk.injEq, true_and, decide_eq_true_eq, eq_iff_iff]
  rcases h2 with h2 | h2
  · have := natCast_inj_of_lt hrp hy h2
    subst this
    rw [if_pos Iff.rfl]
  · by_cases hy0 : y = 0
    · subst hy0
      have : r = 0 := natCast_inj_of_lt hrp (by decide) (by rw [h2, Nat.cast_zero, neg_zero])
      rw [this]
      split_ifs <;> simp only [Nat.sub_zero, Nat.mod_self]
    · have hr' : r = p - y := by
        apply natCast_inj_of_lt hrp (by omega)
        rw [h2, Nat.cast_sub hy.le, cast_p, zero_sub]
      have hpar : (r % 2 = 1) ↔ ¬ (y % 2 = 1) := by
        rw [hr']; have := p_odd; omega
      have hpy : (p - r) % p = y := by
        rw [hr', Nat.sub_sub_self hy.le, Nat.mod_eq_of_lt hy]
      have hne : ¬((r % 2 = 1) ↔ (y % 2 = 1)) := by
        intro h
        by_cases hy1 : y % 2 = 1
        · exact hpar.mp (h.mpr hy1) hy1
        · exact hy1 (h.mp (hpar.mpr hy1))
      rw [if_neg hne, hpy]

private theorem onCurve_iff (x y : ℕ) : onCurve (x, y) = true ↔ y * y % p = (x * x * x + 7) % p := by
  simp [onCurve]

private theorem liftXParity_spec (x : ℕ) (odd : Bool) (hx : x < p) (P : ℕ × ℕ)
    (h : liftXParity x odd = some P) : onCurve P = true ∧ P.1 < p ∧ P.2 < p := by
  simp only [liftXParity] at h
  have hrp : powMod (x * x * x + 7) ((p + 1) / 4) p < p := by
    rw [powMod_eq]; exact Nat.mod_lt _ (by decide)
  generalize powMod (x * x * x + 7) ((p + 1) / 4) p = r at h hrp
  split_ifs at h with h1 h2
  · cases h
    exact ⟨(onCurve_iff _ _).mpr h1, hx, hrp⟩
  · cases h
    refine ⟨(onCurve_iff _ _).mpr ?_, hx, Nat.mod_lt _ (by decide)⟩
    rw [natCast_eq_iff] at h1 ⊢
    rw [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_sub hrp.le, cast_p]
    push_cast at h1 ⊢
    linear_combination h1

/-- `cpoint(cbytes(P)) = P` on reduced curve points. -/
theorem solution (P : ℕ × ℕ) (hP : onCurve P = true) (hx : P.1 < p) (hy : P.2 < p) :
    cpoint (cbytes P) = some P := by
  obtain ⟨x, y⟩ := P
  have hl : ∀ t : BitcoinSer.Byte, (t :: xbytes (x, y)).length = 33 := by
    intro t; simp [xbytes, length_be32]
  have hb : beVal (xbytes (x, y)) = x := beVal_be32 x (lt_trans hx p_lt_256)
  have hpar := liftXParity_of_onCurve x y hy hP
  have h2 : BitVec.toNat (2 : BitcoinSer.Byte) = 2 := rfl
  have h3 : BitVec.toNat (3 : BitcoinSer.Byte) = 3 := rfl
  simp only [cpoint, cbytes, BitcoinSig.parsePubkey, hl, hb, if_true, true_and]
  by_cases he : hasEvenY (x, y) = true
  · have hy2 : decide (y % 2 = 1) = false := by
      simp only [hasEvenY, decide_eq_true_eq] at he; simp only [decide_eq_false_iff_not]; omega
    rw [hy2] at hpar
    simp only [he, if_true, h2]
    rw [if_pos (Or.inl trivial), if_pos hx]
    exact hpar
  · have hy2 : decide (y % 2 = 1) = true := by
      simp only [hasEvenY, decide_eq_true_eq] at he; simp only [decide_eq_true_eq]; omega
    rw [hy2] at hpar
    simp only [Bool.not_eq_true] at he
    simp only [he, h3, Bool.false_eq_true, if_false]
    rw [if_pos (Or.inr trivial), if_pos hx]
    exact hpar
