-- Prove2me | solution 1 for BitcoinMuSig.frost_sign_partialVerify
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T03:53:04.661569+00:00
-- url     : https://prove2.me/submissions/5bf98804-7c5b-4f51-a4de-a4c3882fbcd5

import Definitions.Def_BitcoinMuSig
import Mathlib
import Theorems.Thm_BitcoinMuSig_cpoint_cbytes
import Theorems.Thm_BitcoinMuSig_cpoint_spec
import Theorems.Thm_BitcoinMuSig_n_nsmul_Gpt
import Theorems.Thm_BitcoinMuSig_toPoint_pneg
import Theorems.Thm_BitcoinMuSig_tp_G
import Theorems.Thm_BitcoinMuSig_tp_padd
import Theorems.Thm_BitcoinMuSig_tp_pmul
import Theorems.Thm_BitcoinMuSig_valid_padd
import Theorems.Thm_BitcoinMuSig_valid_pmul

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

private theorem vr_none : Valid none ∧ Reduced none :=
  ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

private theorem vr_cpoint {b : BitcoinSer.Bytes} {P : ℕ × ℕ} (h : cpoint b = some P) :
    Valid (some P) ∧ Reduced (some P) := by
  obtain ⟨h1, h2, h3⟩ := cpoint_spec b P h
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩ <;> cases hxy
  · exact h1
  · exact ⟨h2, h3⟩

private theorem vr_padd {P Q : Point} (hP : Valid P ∧ Reduced P) (hQ : Valid Q ∧ Reduced Q) :
    Valid (padd P Q) ∧ Reduced (padd P Q) :=
  ⟨valid_padd _ _ hP.1 hQ.1, reduced_padd _ _ hP.2 hQ.2⟩

private theorem vr_pmul {k : ℕ} {P : Point} (hP : Valid P ∧ Reduced P) (hk : k < n) :
    Valid (pmul k P) ∧ Reduced (pmul k P) :=
  ⟨valid_pmul _ _ hP.1 (lt_trans hk n_lt_257), reduced_pmul _ _ hP.2⟩

private theorem vr_pneg {P : Point} (hP : Valid P ∧ Reduced P) : Valid (pneg P) ∧ Reduced (pneg P) :=
  ⟨valid_pneg _ hP.1, reduced_pneg _ hP.2⟩

private theorem vr_G : Valid G ∧ Reduced G :=
  ⟨fun x y h => by cases h; decide, fun x y h => by cases h; decide⟩

private theorem tp_pmul' {k : ℕ} {P : Point} (hP : Valid P) (hk : k < n) : tp (pmul k P) = k • tp P :=
  tp_pmul _ _ hP (lt_trans hk n_lt_257)

private theorem keyAggCoeff_lt (pks : List BitcoinSer.Bytes) (pk : BitcoinSer.Bytes) :
    keyAggCoeff pks pk < n := by
  simp only [keyAggCoeff, keyAggCoeffInternal]
  split_ifs
  · unfold n; norm_num
  · exact Nat.mod_lt _ n_pos

private theorem keyAggSum_spec (pks : List BitcoinSer.Bytes) : ∀ (l : List BitcoinSer.Bytes) (T : Point),
    keyAggSum pks l = some T → (Valid T ∧ Reduced T) ∧
      tp T = (l.map fun pk => keyAggCoeff pks pk • tp (cpoint pk)).sum := by
  intro l
  induction l with
  | nil => intro T h; cases h; exact ⟨vr_none, rfl⟩
  | cons pk rest ih =>
    intro T h
    simp only [keyAggSum] at h
    cases hc : cpoint pk with
    | none => simp [hc] at h
    | some P =>
      cases hr : keyAggSum pks rest with
      | none => simp [hc, hr] at h
      | some acc =>
        simp only [hc, hr, Option.some.injEq] at h
        subst h
        obtain ⟨hvr, ht⟩ := ih acc hr
        have hP := vr_cpoint hc
        refine ⟨vr_padd (vr_pmul hP (keyAggCoeff_lt _ _)) hvr, ?_⟩
        rw [tp_padd _ _ (vr_pmul hP (keyAggCoeff_lt _ _)).1 hvr.1, tp_pmul' hP.1 (keyAggCoeff_lt _ _), ht]
        simp [hc]

private theorem nonceSum_spec (j : ℕ) : ∀ (l : List BitcoinSer.Bytes) (T : Point),
    nonceSum j l = some T → (Valid T ∧ Reduced T) ∧
      tp T = (l.map fun pn => tp (cpoint ((pn.drop (33 * j)).take 33))).sum := by
  intro l
  induction l with
  | nil => intro T h; cases h; exact ⟨vr_none, rfl⟩
  | cons pn rest ih =>
    intro T h
    simp only [nonceSum] at h
    cases hc : cpoint ((pn.drop (33 * j)).take 33) with
    | none => simp [hc] at h
    | some P =>
      cases hr : nonceSum j rest with
      | none => simp [hc, hr] at h
      | some acc =>
        simp only [hc, hr, Option.some.injEq] at h
        subst h
        obtain ⟨hvr, ht⟩ := ih acc hr
        have hP := vr_cpoint hc
        refine ⟨vr_padd hP hvr, ?_⟩
        rw [tp_padd _ _ hP.1 hvr.1, ht]
        simp [hc]

private theorem mod_nsmul {T : W.Point} (hT : n • T = 0) (k : ℕ) : (k % n) • T = k • T := by
  conv_rhs => rw [← Nat.div_add_mod k n]
  rw [add_nsmul, mul_nsmul, hT, nsmul_zero, zero_add]

private theorem sub_nsmul' {T : W.Point} (hT : n • T = 0) (e : ℕ) (he : e < n) :
    ((n - e) % n) • T = -(e • T) := by
  rw [mod_nsmul hT, eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel he.le, hT]

private theorem tor_add {A B : W.Point} (hA : n • A = 0) (hB : n • B = 0) : n • (A + B) = 0 := by
  rw [nsmul_add, hA, hB, add_zero]

private theorem tor_nsmul {A : W.Point} (hA : n • A = 0) (k : ℕ) : n • (k • A) = 0 := by
  rw [← mul_nsmul', mul_comm, mul_nsmul', hA, nsmul_zero]

private theorem tor_neg {A : W.Point} (hA : n • A = 0) : n • (-A) = 0 := by
  simp [hA]

private theorem tor_list_sum {α : Type*} (l : List α) (f : α → W.Point) (h : ∀ x ∈ l, n • f x = 0) :
    n • (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons]
    exact tor_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem tweak_step (Q0 : W.Point) (hQ0 : n • Q0 = 0) (ctx : KeyAggCtx)
    (g t : ℕ) (hg : g < n) (ht : t < n) (Q' : ℕ × ℕ)
    (hQ : padd (pmul g (some ctx.Q)) (pmul t G) = some Q')
    (hv : Valid (some ctx.Q) ∧ Reduced (some ctx.Q)) (hq : tp (some ctx.Q) = ctx.gacc • Q0 + ctx.tacc • Gpt) :
    (Valid (some Q') ∧ Reduced (some Q')) ∧
      tp (some Q') = (g * ctx.gacc % n) • Q0 + ((t + g * ctx.tacc) % n) • Gpt := by
  have hvQ := vr_padd (vr_pmul hv hg) (vr_pmul vr_G ht)
  have htQ := tp_padd _ _ (vr_pmul hv hg).1 (vr_pmul vr_G ht).1
  rw [hQ] at hvQ htQ
  refine ⟨hvQ, ?_⟩
  rw [htQ, tp_pmul' hv.1 hg, tp_pmul' vr_G.1 ht, hq, tp_G, mod_nsmul hQ0, mod_nsmul n_nsmul_Gpt, nsmul_add,
    add_nsmul, mul_nsmul', mul_nsmul']
  abel

private theorem applyTweaks_spec (Q0 : W.Point) (hQ0 : n • Q0 = 0) :
    ∀ (tws : List (BitcoinSer.Bytes × Bool)) (ctx ctx' : KeyAggCtx),
    applyTweaks ctx tws = some ctx' → (Valid (some ctx.Q) ∧ Reduced (some ctx.Q)) →
    tp (some ctx.Q) = ctx.gacc • Q0 + ctx.tacc • Gpt →
    (Valid (some ctx'.Q) ∧ Reduced (some ctx'.Q)) ∧ tp (some ctx'.Q) = ctx'.gacc • Q0 + ctx'.tacc • Gpt := by
  intro tws
  induction tws with
  | nil => intro ctx ctx' h hv ht; cases h; exact ⟨hv, ht⟩
  | cons tw rest ih =>
    intro ctx ctx' h hv ht
    obtain ⟨tw, x⟩ := tw
    simp only [applyTweaks] at h
    cases h1 : applyTweak ctx tw x with
    | none => simp [h1] at h
    | some c1 =>
      simp only [h1] at h
      have hn1 : n - 1 < n := Nat.sub_lt n_pos one_pos
      have h1n : 1 < n := one_lt_n
      simp only [applyTweak] at h1
      split_ifs at h1 with ht' hx
      · cases hQ : padd (pmul (n - 1) (some ctx.Q)) (pmul (beVal tw) G) with
        | none => simp [hQ] at h1
        | some Q' =>
          simp only [hQ, Option.some.injEq] at h1
          subst h1
          obtain ⟨hv1, ht1⟩ := tweak_step Q0 hQ0 ctx (n - 1) _ hn1 (not_le.mp ht') Q' hQ hv ht
          exact ih _ ctx' h hv1 ht1
      · cases hQ : padd (pmul 1 (some ctx.Q)) (pmul (beVal tw) G) with
        | none => simp [hQ] at h1
        | some Q' =>
          simp only [hQ, Option.some.injEq] at h1
          subst h1
          obtain ⟨hv1, ht1⟩ := tweak_step Q0 hQ0 ctx 1 _ h1n (not_le.mp ht') Q' hQ hv ht
          exact ih _ ctx' h hv1 ht1

private theorem keyAggTweaked_spec (pks : List BitcoinSer.Bytes)
    (hkeys : ∀ pk ∈ pks, n • tp (cpoint pk) = 0)
    (tws : List (BitcoinSer.Bytes × Bool)) (kctx : KeyAggCtx) (h : keyAggTweaked pks tws = some kctx) :
    (Valid (some kctx.Q) ∧ Reduced (some kctx.Q)) ∧
      tp (some kctx.Q) = kctx.gacc • (pks.map fun pk => keyAggCoeff pks pk • tp (cpoint pk)).sum +
        kctx.tacc • Gpt := by
  simp only [keyAggTweaked] at h
  cases hk : keyAgg pks with
  | none => simp [hk] at h
  | some c0 =>
    simp only [hk] at h
    simp only [keyAgg] at hk
    cases hs : keyAggSum pks pks with
    | none => simp [hs] at hk
    | some T =>
      cases T with
      | none => simp [hs] at hk
      | some Q =>
        simp only [hs, Option.some.injEq] at hk
        subst hk
        obtain ⟨hv, ht⟩ := keyAggSum_spec pks pks _ hs
        exact applyTweaks_spec _ (tor_list_sum _ _ fun pk hpk => tor_nsmul (hkeys pk hpk) _) tws _ kctx h hv
          (by rw [ht]; simp)

private theorem length_cbytesExt (R : Point) : (cbytesExt R).length = 33 := by
  rcases R with _ | P
  · rfl
  · simp [cbytesExt, cbytes, xbytes, length_be32]

private theorem cpointExt_cbytesExt (R : Point) (hR : Valid R ∧ Reduced R) :
    cpointExt (cbytesExt R) = some R := by
  rcases R with _ | ⟨x, y⟩
  · simp [cbytesExt, cpointExt]
  · have hne : cbytesExt (some (x, y)) ≠ zero33 := by
      simp only [cbytesExt, cbytes, zero33]
      intro h
      have h0 := congrArg List.head? h
      simp only [List.head?_cons] at h0
      rw [List.replicate_succ, List.head?_cons] at h0
      split_ifs at h0 <;> simp at h0
    simp only [cpointExt, hne, if_false]
    rw [show cbytesExt (some (x, y)) = cbytes (x, y) from rfl,
      cpoint_cbytes (x, y) (hR.1 x y rfl) (hR.2 x y rfl).1 (hR.2 x y rfl).2]
    rfl

private theorem take_drop_append (A B : BitcoinSer.Bytes) (hA : A.length = 33) (hB : B.length = 33) :
    (A ++ B).take 33 = A ∧ ((A ++ B).drop 33).take 33 = B := by
  constructor
  · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
      List.take_of_length_le (by omega)]

private theorem getSessionValues_spec (ctx : SessionCtx) (sv : SessionValues)
    (h : getSessionValues ctx = some sv) :
    ∃ kctx R1 R2, keyAggTweaked ctx.pks ctx.tweaks = some kctx ∧ sv.Q = kctx.Q ∧ sv.gacc = kctx.gacc ∧
      sv.tacc = kctx.tacc ∧ sv.b < n ∧ cpointExt (ctx.aggnonce.take 33) = some R1 ∧
      cpointExt ((ctx.aggnonce.drop 33).take 33) = some R2 ∧ sv.R' = padd R1 (pmul sv.b R2) ∧
      (∀ R, sv.R' = some R → sv.R = R) ∧
      sv.e = beVal (BitcoinMuSig.tagged "BIP0340/challenge" (xbytes sv.R ++ xbytes sv.Q ++ ctx.msg)) % n := by
  simp only [getSessionValues] at h
  cases hk : keyAggTweaked ctx.pks ctx.tweaks with
  | none => simp [hk] at h
  | some kctx =>
    simp only [hk] at h
    cases h1 : cpointExt (ctx.aggnonce.take 33) with
    | none => simp [h1] at h
    | some R1 =>
      cases h2 : cpointExt ((ctx.aggnonce.drop 33).take 33) with
      | none => simp [h1, h2] at h
      | some R2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        refine ⟨kctx, R1, R2, rfl, rfl, rfl, rfl, Nat.mod_lt _ n_pos, rfl, rfl, rfl, ?_, rfl⟩
        intro R hR
        simp only at hR ⊢
        rw [hR]

private theorem psv_spec (psig pn pk : BitcoinSer.Bytes) (ctx : SessionCtx)
    (h : partialSigVerifyInternal psig pn pk ctx = true) :
    ∃ sv R1 R2 P, getSessionValues ctx = some sv ∧ psig.length = 32 ∧ beVal psig < n ∧
      cpoint (pn.take 33) = some R1 ∧ cpoint ((pn.drop 33).take 33) = some R2 ∧ cpoint pk = some P ∧
      pmul (beVal psig) G =
        padd (if hasEvenY sv.R then padd (some R1) (pmul sv.b (some R2))
          else pneg (padd (some R1) (pmul sv.b (some R2))))
        (pmul (sv.e * keyAggCoeff ctx.pks pk * ((if hasEvenY sv.Q then 1 else n - 1) * sv.gacc % n) % n)
          (some P)) := by
  simp only [partialSigVerifyInternal] at h
  cases hs : getSessionValues ctx with
  | none => simp [hs] at h
  | some sv =>
    simp only [hs] at h
    by_cases h1 : (psig.length ≠ 32 ∨ n ≤ beVal psig)
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    cases h2 : cpoint (pn.take 33) with
    | none => simp [h2] at h
    | some R1 =>
      cases h3 : cpoint ((pn.drop 33).take 33) with
      | none => simp [h2, h3] at h
      | some R2 =>
        cases h4 : cpoint pk with
        | none => simp [h2, h3, h4] at h
        | some P =>
          simp only [h2, h3, h4] at h
          by_cases h5 : pk ∉ ctx.pks
          · rw [if_pos h5] at h; cases h
          rw [if_neg h5] at h
          refine ⟨sv, R1, R2, P, rfl, ?_, ?_, rfl, rfl, rfl, of_decide_eq_true h⟩
          · by_contra hc; exact h1 (Or.inl hc)
          · by_contra hc; exact h1 (Or.inr (not_lt.mp hc))

private def sgnHom (b : Bool) : W.Point →+ W.Point := if b then AddMonoidHom.id _ else -AddMonoidHom.id _

private theorem sgnHom_true (T : W.Point) : sgnHom true T = T := rfl

private theorem sgnHom_false (T : W.Point) : sgnHom false T = -T := rfl

private theorem list_sum_nsmul {α : Type*} (l : List α) (f : α → ℕ) (T : W.Point) :
    (l.map f).sum • T = (l.map fun x => f x • T).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [add_nsmul, ih]

private theorem list_combo {α : Type*} (l : List α) (s a : α → ℕ) (R1 R2 P : α → W.Point) (b c : ℕ)
    (ε : W.Point →+ W.Point)
    (h : ∀ t ∈ l, s t • Gpt = ε (R1 t + b • R2 t) + (c * a t) • P t) :
    (l.map s).sum • Gpt = ε ((l.map R1).sum + b • (l.map R2).sum) + c • (l.map fun t => a t • P t).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, add_nsmul]
    rw [h x (List.mem_cons_self), ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    simp only [map_add, map_nsmul, nsmul_add, mul_nsmul']
    abel

private theorem nm1_nsmul {T : W.Point} (hT : n • T = 0) : (n - 1) • T = -T := by
  have := sub_nsmul' hT 1 one_lt_n
  rw [Nat.mod_eq_of_lt (Nat.sub_lt n_pos one_pos), one_nsmul] at this
  exact this

private theorem liftX_even (Q : ℕ × ℕ) (hQ : Valid (some Q) ∧ Reduced (some Q))
    (hQt : n • tp (some Q) = 0) :
    ∃ P', liftX Q.1 = some P' ∧ (Valid (some P') ∧ Reduced (some P')) ∧
      tp (some P') = (if hasEvenY Q then 1 else n - 1) • tp (some Q) := by
  obtain ⟨x, y⟩ := Q
  have hx := (hQ.2 x y rfl).1
  have hy := (hQ.2 x y rfl).2
  have hc := hQ.1 x y rfl
  simp only [liftX, if_pos hx]
  by_cases he : hasEvenY (x, y) = true
  · have hy2 : decide (y % 2 = 1) = false := by
      simp only [hasEvenY, decide_eq_true_eq] at he; simp only [decide_eq_false_iff_not]; omega
    have := liftXParity_of_onCurve x y hy hc
    rw [hy2] at this
    exact ⟨(x, y), this, hQ, by rw [if_pos he, one_nsmul]⟩
  · have hy1 : y % 2 = 1 := by simp only [hasEvenY, decide_eq_true_eq] at he; omega
    have hneg := vr_pneg hQ
    have hpn : pneg (some (x, y)) = some (x, p - y) := by
      simp only [pneg, Nat.mod_eq_of_lt hy]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hpn] at hneg
    have hpar : decide ((p - y) % 2 = 1) = false := by
      simp only [decide_eq_false_iff_not]; have := p_odd; omega
    have := liftXParity_of_onCurve x (p - y) (by omega) (hneg.1 x (p - y) rfl)
    rw [hpar] at this
    refine ⟨(x, p - y), this, hneg, ?_⟩
    rw [if_neg he, nm1_nsmul hQt, ← hpn, tp_pneg _ hQ.1]

private theorem signer_eq (psig pn pk : BitcoinSer.Bytes)
    (ctx : SessionCtx) (sv : SessionValues) (hs : getSessionValues ctx = some sv)
    (hkey : n • tp (cpoint pk) = 0)
    (h : partialSigVerifyInternal psig pn pk ctx = true) :
    psig.length = 32 ∧ beVal psig < n ∧ (∃ R1, cpoint (pn.take 33) = some R1) ∧
      (∃ R2, cpoint ((pn.drop 33).take 33) = some R2) ∧ (∃ P, cpoint pk = some P) ∧
      (beVal psig) • Gpt = sgnHom (hasEvenY sv.R)
        (tp (cpoint (pn.take 33)) + sv.b • tp (cpoint ((pn.drop 33).take 33))) +
        (sv.e * (if hasEvenY sv.Q then 1 else n - 1) * sv.gacc * keyAggCoeff ctx.pks pk) • tp (cpoint pk) := by
  obtain ⟨sv', R1, R2, P, hs', hl, hlt, h2, h3, h4, heq⟩ := psv_spec psig pn pk ctx h
  rw [hs] at hs'
  cases hs'
  refine ⟨hl, hlt, ⟨R1, h2⟩, ⟨R2, h3⟩, ⟨P, h4⟩, ?_⟩
  rw [h2, h3, h4]
  have hb : sv.b < n := by
    obtain ⟨_, _, _, _, _, _, _, hb, _⟩ := getSessionValues_spec ctx sv hs; exact hb
  have hR1 := vr_cpoint h2
  have hR2 := vr_cpoint h3
  have hP := vr_cpoint h4
  have hRe := vr_padd hR1 (vr_pmul hR2 hb)
  have hc : (sv.e * keyAggCoeff ctx.pks pk * ((if hasEvenY sv.Q then 1 else n - 1) * sv.gacc % n) % n) < n :=
    Nat.mod_lt _ n_pos
  have hRe' : Valid (if hasEvenY sv.R then padd (some R1) (pmul sv.b (some R2))
      else pneg (padd (some R1) (pmul sv.b (some R2)))) := by
    split_ifs
    · exact hRe.1
    · exact (vr_pneg hRe).1
  have hPt : n • tp (some P) = 0 := by rw [← h4]; exact hkey
  have hcoef : ∀ (g : ℕ), ((sv.e * keyAggCoeff ctx.pks pk * (g * sv.gacc % n)) % n) • tp (some P) =
      (sv.e * g * sv.gacc * keyAggCoeff ctx.pks pk) • tp (some P) := by
    intro g
    generalize tp (some P) = T at hPt ⊢
    rw [mod_nsmul hPt, ← mod_nsmul hPt (sv.e * keyAggCoeff ctx.pks pk * (g * sv.gacc % n)), Nat.mul_mod_mod,
      mod_nsmul hPt]
    generalize keyAggCoeff ctx.pks pk = a
    rw [show sv.e * a * (g * sv.gacc) = sv.e * g * sv.gacc * a by ring]
  have := congrArg tp heq
  rw [tp_pmul' vr_G.1 hlt, tp_G, tp_padd _ _ hRe' (vr_pmul hP hc).1, tp_pmul' hP.1 hc, hcoef] at this
  have hfirst : tp (if hasEvenY sv.R then padd (some R1) (pmul sv.b (some R2))
      else pneg (padd (some R1) (pmul sv.b (some R2)))) =
      sgnHom (hasEvenY sv.R) (tp (some R1) + sv.b • tp (some R2)) := by
    cases hb' : hasEvenY sv.R
    · simp only [Bool.false_eq_true, if_false]
      rw [tp_pneg _ hRe.1, tp_padd _ _ hR1.1 (vr_pmul hR2 hb).1, tp_pmul' hR2.1 hb, sgnHom_false]
    · simp only [if_true]
      rw [tp_padd _ _ hR1.1 (vr_pmul hR2 hb).1, tp_pmul' hR2.1 hb, sgnHom_true]
  rewrite [this, hfirst]
  rfl

set_option maxRecDepth 100000 in

private theorem nprime_1627771 : Nat.Prime 1627771 := by norm_num

set_option maxRecDepth 100000 in

private theorem nprime_4681609 : Nat.Prime 4681609 := by norm_num

set_option maxRecDepth 100000 in

private theorem nprime_44706919 : Nat.Prime 44706919 := by
  refine prime_of_cert _ 6 [2, 3, 797, 9349] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> first | norm_num

set_option maxRecDepth 100000 in

private theorem nprime_545358713 : Nat.Prime 545358713 := by
  refine prime_of_cert _ 5 [2, 2, 2, 41, 59, 28181] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | norm_num

set_option maxRecDepth 100000 in

private theorem nprime_297159362677 : Nat.Prime 297159362677 := by
  refine prime_of_cert _ 2 [2, 2, 3, 3, 11, 461, 1627771] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact nprime_1627771 | norm_num

set_option maxRecDepth 100000 in

private theorem nprime_107361793816595537 : Nat.Prime 107361793816595537 := by
  refine prime_of_cert _ 3 [2, 2, 2, 2, 16699, 85831, 4681609] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact nprime_4681609 | norm_num

set_option maxRecDepth 100000 in

private theorem nprime_174723607534414371449 : Nat.Prime 174723607534414371449 := by
  refine prime_of_cert _ 3 [2, 2, 2, 17, 59, 4051, 120233, 44706919] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact nprime_44706919 | norm_num

set_option maxRecDepth 100000 in

private theorem nprime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 := by
  refine prime_of_cert _ 2 [2, 293, 305873, 545358713, 297159362677] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> first | exact nprime_545358713 | exact nprime_297159362677 | norm_num

set_option maxRecDepth 100000 in

private theorem nprime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 := by
  refine prime_of_cert _ 2 [2, 2, 3, 3, 3, 109, 29047611873442575647497758179] (by norm_num) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact nprime_29047611873442575647497758179 | norm_num

set_option maxRecDepth 100000 in

private theorem n_prime_cert : Nat.Prime n := by
  refine prime_of_cert _ 7 [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449, 341948486974166000522343609283189]
    (by decide) ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact nprime_107361793816595537
      | exact nprime_174723607534414371449
      | exact nprime_341948486974166000522343609283189
      | norm_num

private theorem lagrange_zero {F ι : Type*} [Field F] [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (f : Polynomial F) (hdeg : f.degree < s.card) :
    ∑ i ∈ s, (∏ j ∈ s.erase i, v j * (v j - v i)⁻¹) * f.eval (v i) = f.eval 0 := by
  conv_rhs => rw [Lagrange.eq_interpolate hvs hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.basis, Polynomial.eval_prod, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, ← neg_sub (v j) (v i), inv_neg]
  ring

/-- FROST signing produces a share passing the partial verification: with nonces `d, e`
(`D = d⋅G`, `E = e⋅G`) and secret share `s` (`Y = s⋅G`), `z = d + e⋅ρ + λ⋅s⋅c` satisfies
`z⋅G = D + ρ⋅E + (c⋅λ)⋅Y`. -/
theorem solution {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (G : M) (d e ρ lam s c : K) :
    (d + e * ρ + lam * s * c) • G = d • G + ρ • (e • G) + (c * lam) • (s • G) := by
  module
