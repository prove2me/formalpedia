-- Prove2me | solution 1 for Erdos195.extremes_val_ne
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:07:34.299685+00:00
-- url     : https://prove2.me/submissions/cd53deb0-f1ce-4ffb-9ea2-8aa1b4223eed

import Mathlib
import Definitions.Def_Erdos195_defs


/-!
# Erdős #195 — ε-orders on ℤ: alternating-bit lemma, 3AP-freeness, and the (*) identity

For `ε : ℕ → Bool`, `epsLt ε x y` means `x ≠ y` and, at `k = ν₂(y - x)` (the least
binary digit where `x` and `y` differ), the `k`-th two's-complement digit of `x`
is `1` exactly when `ε k = true`. With `ε ≡ true` this is the order `◁` used by Ho
(arXiv:2609.12780) extended to ℤ (the binary chaotic order of Ardal–Brown–Jungić, dualised).
-/

namespace E195Aux

/-- The `k`-th binary digit of an integer (two's complement), as a proposition "digit = 1". -/
def bitOne (x : ℤ) (k : ℕ) : Prop := x / 2 ^ k % 2 = 1

/-- The ε-order on ℤ. -/
def epsLt (ε : ℕ → Bool) (x y : ℤ) : Prop :=
  x ≠ y ∧ (bitOne x (padicValInt 2 (y - x)) ↔ ε (padicValInt 2 (y - x)) = true)

/-- `2 ^ ν₂ r ∣ r`. -/
lemma two_pow_val_dvd (r : ℤ) : (2 : ℤ) ^ padicValInt 2 r ∣ r := by
  have := padicValInt_dvd (p := 2) r
  simpa using this

/-- The odd part `r / 2 ^ ν₂ r` is odd. -/
lemma odd_part (r : ℤ) (hr : r ≠ 0) : r / 2 ^ padicValInt 2 r % 2 = 1 := by
  by_contra h
  have h2 : (2 : ℤ) ∣ r / 2 ^ padicValInt 2 r := by omega
  obtain ⟨s, hs⟩ := h2
  have hr' : r = 2 ^ padicValInt 2 r * (r / 2 ^ padicValInt 2 r) :=
    (Int.mul_ediv_cancel' (two_pow_val_dvd r)).symm
  have hd : ((2 : ℕ) : ℤ) ^ (padicValInt 2 r + 1) ∣ r := ⟨s, by
    push_cast
    calc r = 2 ^ padicValInt 2 r * (r / 2 ^ padicValInt 2 r) := hr'
      _ = 2 ^ (padicValInt 2 r + 1) * s := by rw [hs]; ring⟩
  rcases (padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) _ r).1 hd with h0 | h0
  · exact hr h0
  · omega

/-- Alternating-bit lemma: the digit at `ν₂ r` along an AP. -/
lemma div_pow_add_mul (a r j : ℤ) :
    (a + j * r) / 2 ^ padicValInt 2 r = a / 2 ^ padicValInt 2 r + j * (r / 2 ^ padicValInt 2 r) := by
  have h : (2 : ℤ) ^ padicValInt 2 r ≠ 0 := pow_ne_zero _ (by norm_num)
  have e : a + j * r = a + (j * (r / 2 ^ padicValInt 2 r)) * 2 ^ padicValInt 2 r := by
    rw [mul_assoc, Int.ediv_mul_cancel (two_pow_val_dvd r)]
  rw [e, Int.add_mul_ediv_right _ _ h]

/-- Comparison of consecutive AP terms `a + j r`, `a + (j+1) r` in the ε-order. -/
lemma epsLt_step (ε : ℕ → Bool) {a r : ℤ} (hr : r ≠ 0) (j : ℤ) :
    epsLt ε (a + j * r) (a + (j + 1) * r) ↔
      ((a / 2 ^ padicValInt 2 r + j * (r / 2 ^ padicValInt 2 r)) % 2 = 1 ↔
        ε (padicValInt 2 r) = true) := by
  have hdiff : a + (j + 1) * r - (a + j * r) = r := by ring
  unfold epsLt bitOne
  rw [hdiff, div_pow_add_mul]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by intro h'; apply hr; linarith, h⟩

/-- Helper: parity of `A + j q` for `q` odd. -/
lemma parity_alt {A q : ℤ} (hq : q % 2 = 1) (j : ℤ) :
    ((A + (j + 1) * q) % 2 = 1 ↔ ¬ (A + j * q) % 2 = 1) := by
  have : A + (j + 1) * q = (A + j * q) + q := by ring
  rw [this]; omega

/-- **No monotone 3AP** in any ε-order (covers increasing and decreasing APs, `r` of any sign). -/
theorem epsLt_no_3AP (ε : ℕ → Bool) {a r : ℤ} (hr : r ≠ 0) :
    ¬ (epsLt ε a (a + r) ∧ epsLt ε (a + r) (a + 2 * r)) := by
  rintro ⟨h1, h2⟩
  have e1 := (epsLt_step ε (a := a) hr 0).1 (by simpa using h1)
  have e2 := (epsLt_step ε (a := a) hr 1).1 (by
    have : a + 1 * r = a + r := by ring
    have h' : a + (1 + 1) * r = a + 2 * r := by ring
    rw [this, h']; exact h2)
  have hq1 := odd_part r hr
  have := parity_alt (A := a / 2 ^ padicValInt 2 r) hq1 0
  simp only [zero_add, one_mul, zero_mul, add_zero] at this e1 e2
  tauto

/-- **The (*) identity**: `a ≺ a+r ↔ a+2r ≺ a+3r` in any ε-order. -/
theorem epsLt_star (ε : ℕ → Bool) {a r : ℤ} (hr : r ≠ 0) :
    epsLt ε a (a + r) ↔ epsLt ε (a + 2 * r) (a + 3 * r) := by
  have h0 := epsLt_step ε (a := a) hr 0
  have h2 := epsLt_step ε (a := a) hr 2
  simp only [zero_mul, add_zero, zero_add, one_mul] at h0
  have e2 : a + (2 + 1) * r = a + 3 * r := by ring
  rw [e2] at h2
  rw [h0, h2]
  have : (a / 2 ^ padicValInt 2 r + 2 * (r / 2 ^ padicValInt 2 r)) % 2 =
      (a / 2 ^ padicValInt 2 r) % 2 := by omega
  rw [this]


/-- The order of the completion `C(P)`. -/
def compLt (R : ℤ → ℤ → Prop) (P : List ℤ) (x y : ℤ) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ P.idxOf x < P.idxOf y) ∨ (x ∈ P ∧ y ∉ P) ∨ (x ∉ P ∧ y ∉ P ∧ R x y)

/-- `P` is safe: its completion has no monotone 4AP. -/
def Safe (R : ℤ → ℤ → Prop) (P : List ℤ) : Prop :=
  ∀ a r : ℤ, r ≠ 0 →
    ¬ (compLt R P a (a + r) ∧ compLt R P (a + r) (a + 2 * r) ∧ compLt R P (a + 2 * r) (a + 3 * r))

/-- (A): no monotone 3AP. -/
def No3AP (R : ℤ → ℤ → Prop) : Prop :=
  ∀ a r : ℤ, r ≠ 0 → ¬ (R a (a + r) ∧ R (a + r) (a + 2 * r))

/-- (B): the (*) identity. -/
def Star (R : ℤ → ℤ → Prop) : Prop :=
  ∀ a r : ℤ, r ≠ 0 → (R a (a + r) ↔ R (a + 2 * r) (a + 3 * r))

lemma pairwise_idx {S : ℤ → ℤ → Prop} {P : List ℤ} (hP : P.Pairwise S) {x y : ℤ}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : P.idxOf x < P.idxOf y) : S x y := by
  have hxl := List.idxOf_lt_length_of_mem hx
  have hyl := List.idxOf_lt_length_of_mem hy
  have := List.pairwise_iff_getElem.1 hP _ _ hxl hyl hxy
  rwa [List.getElem_idxOf hxl, List.getElem_idxOf hyl] at this

/-- **Reverse-order safety** (abstract form of Ho's Lemma 1): if `R` is asymmetric, has no
monotone 3AP and satisfies (*), then any finite word listed in *reverse* `R`-order is safe. -/
theorem safe_of_pairwise_rev {R : ℤ → ℤ → Prop} (hA : No3AP R) (hB : Star R)
    (hasymm : ∀ x y, R x y → ¬ R y x) {P : List ℤ} (hP : P.Pairwise (fun x y => R y x)) :
    Safe R P := by
  intro a r hr ⟨h1, h2, h3⟩
  have hA' : ¬ (R (a + 2 * r) (a + r) ∧ R (a + r) a) := by
    have := hA (a + 2 * r) (-r) (neg_ne_zero.mpr hr)
    have e1 : a + 2 * r + -r = a + r := by ring
    have e2 : a + 2 * r + 2 * -r = a := by ring
    rwa [e1, e2] at this
  have hA1 : ¬ (R (a + r) (a + 2 * r) ∧ R (a + 2 * r) (a + 3 * r)) := by
    have := hA (a + r) r hr
    have e1 : a + r + r = a + 2 * r := by ring
    have e2 : a + r + 2 * r = a + 3 * r := by ring
    rwa [e1, e2] at this
  rcases h1 with ⟨p0, p1, i01⟩ | ⟨p0, n1⟩ | ⟨n0, n1, r01⟩ <;>
  rcases h2 with ⟨q1, p2, i12⟩ | ⟨q1, n2⟩ | ⟨m1, n2, r12⟩ <;>
  rcases h3 with ⟨q2, p3, i23⟩ | ⟨q2, n3⟩ | ⟨m2, n3, r23⟩ <;>
  first
  | contradiction
  | exact hA' ⟨pairwise_idx hP q1 p2 i12, pairwise_idx hP p0 p1 i01⟩
  | exact hA1 ⟨r12, r23⟩
  | exact hasymm _ _ ((hB a r hr).2 r23) (pairwise_idx hP p0 p1 i01)

/-- **Extremum obstruction.** Suppose `R` satisfies (*) and has a least element `z`
(`R z y` for all `y ≠ z`). If `z` occurs in a safe word `P`, then no element occurring
after `z` in `P` can be the maximum or the minimum of `P`.
Witness: the 4AP `z, M, 2M - z, 3M - 2z`. -/
theorem extremum_obstruction {R : ℤ → ℤ → Prop} (hB : Star R) {z : ℤ}
    (hz : ∀ y, y ≠ z → R z y) {P : List ℤ} (hS : Safe R P) (hzP : z ∈ P) {M : ℤ}
    (hMP : M ∈ P) (hzM : P.idxOf z < P.idxOf M)
    (hext : (∀ x ∈ P, x ≤ M) ∨ (∀ x ∈ P, M ≤ x)) : False := by
  have hMz : M ≠ z := by rintro rfl; exact lt_irrefl _ hzM
  have hr : M - z ≠ 0 := sub_ne_zero.mpr hMz
  have e1 : z + (M - z) = M := by ring
  have hout : z + 2 * (M - z) ∉ P ∧ z + 3 * (M - z) ∉ P := by
    rcases hext with h | h
    · have hzle := h z hzP
      have hlt : z < M := lt_of_le_of_ne hzle (Ne.symm hMz)
      constructor <;> intro hm <;> have := h _ hm <;> linarith
    · have hzle := h z hzP
      have hlt : M < z := lt_of_le_of_ne hzle hMz
      constructor <;> intro hm <;> have := h _ hm <;> linarith
  have hR : R (z + 2 * (M - z)) (z + 3 * (M - z)) := by
    have := (hB z (M - z) hr).1
    rw [e1] at this
    exact this (hz M hMz)
  apply hS z (M - z) hr
  rw [e1]
  refine ⟨Or.inl ⟨hzP, hMP, hzM⟩, Or.inr (Or.inl ⟨hMP, hout.1⟩),
    Or.inr (Or.inr ⟨hout.1, hout.2, hR⟩)⟩

lemma prefix_mono {P : ℕ → List ℤ} (hpre : ∀ n, P n <+: P (n + 1)) {m n : ℕ} (h : m ≤ n) :
    P m <+: P n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (hpre n)

/-- **No exhaustive chain of safe words.** If `R` satisfies (*) and has a least element, there is
no increasing (prefix-ordered) sequence of safe words whose union is all of ℤ. In particular,
Ho's method cannot be run on ℤ with a *fixed* completion order having a least element
(e.g. the two's-complement order `◁`, whose least element is `-1`). -/
theorem no_exhaustive_safe_chain {R : ℤ → ℤ → Prop} (hB : Star R) {z : ℤ}
    (hz : ∀ y, y ≠ z → R z y) (P : ℕ → List ℤ) (hsafe : ∀ n, Safe R (P n))
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x, ∃ n, x ∈ P n) : False := by
  obtain ⟨n0, hz0⟩ := hcov z
  have hne0 : (P n0).toFinset.Nonempty := ⟨z, List.mem_toFinset.2 hz0⟩
  set b := (P n0).toFinset.max' hne0 with hb
  obtain ⟨n1, hx1⟩ := hcov (b + 1)
  set n := max n0 n1
  obtain ⟨t, ht⟩ := prefix_mono hpre (le_max_left n0 n1)
  have hx : b + 1 ∈ P n := (prefix_mono hpre (le_max_right n0 n1)).subset hx1
  have hzn : z ∈ P n := by rw [← ht]; exact List.mem_append_left _ hz0
  have hne : (P n).toFinset.Nonempty := ⟨z, List.mem_toFinset.2 hzn⟩
  set M := (P n).toFinset.max' hne with hM
  have hMP : M ∈ P n := List.mem_toFinset.1 (Finset.max'_mem _ _)
  have hmax : ∀ x ∈ P n, x ≤ M := fun x hx => Finset.le_max' _ x (List.mem_toFinset.2 hx)
  have hbM : b < M := by have := hmax _ hx; linarith
  have hM0 : M ∉ P n0 := by
    intro h
    have := Finset.le_max' _ M (List.mem_toFinset.2 h)
    rw [← hb] at this
    linarith
  have hidx : (P n).idxOf z < (P n).idxOf M := by
    rw [← ht, List.idxOf_append, List.idxOf_append, if_pos hz0, if_neg hM0]
    have := List.idxOf_lt_length_of_mem hz0
    omega
  exact extremum_obstruction hB hz (hsafe n) hzn hMP hidx (Or.inl hmax)

/-! ## Instances: ε-orders satisfy the abstract hypotheses -/

lemma padicValInt_sub_comm (x y : ℤ) : padicValInt 2 (x - y) = padicValInt 2 (y - x) := by
  rw [padicValInt, padicValInt, ← Int.natAbs_neg, neg_sub]

/-- ε-orders are asymmetric. -/
theorem epsLt_asymm (ε : ℕ → Bool) {x y : ℤ} (h : epsLt ε x y) : ¬ epsLt ε y x := by
  rintro ⟨hne, h'⟩
  obtain ⟨-, h⟩ := h
  rw [padicValInt_sub_comm] at h'
  have hr : y - x ≠ 0 := sub_ne_zero.mpr hne
  have hq := odd_part (y - x) hr
  have hy := div_pow_add_mul x (y - x) 1
  rw [show x + 1 * (y - x) = y by ring, one_mul] at hy
  unfold bitOne at h h'
  rw [hy] at h'
  have key : (x / 2 ^ padicValInt 2 (y - x) + (y - x) / 2 ^ padicValInt 2 (y - x)) % 2 = 1 ↔
      ¬ x / 2 ^ padicValInt 2 (y - x) % 2 = 1 := by omega
  tauto

theorem epsLt_no3AP (ε : ℕ → Bool) : No3AP (epsLt ε) := fun _ _ hr => epsLt_no_3AP ε hr

theorem epsLt_star' (ε : ℕ → Bool) : Star (epsLt ε) := fun _ _ hr => epsLt_star ε hr

/-- Reverse-order safety for every ε-order. -/
theorem epsLt_safe_of_rev (ε : ℕ → Bool) {P : List ℤ}
    (hP : P.Pairwise (fun x y => epsLt ε y x)) : Safe (epsLt ε) P :=
  safe_of_pairwise_rev (epsLt_no3AP ε) (epsLt_star' ε) (fun _ _ h => epsLt_asymm ε h) hP

/-- In the two's-complement order (`ε ≡ true`, Ho's `◁` on ℤ), `-1` is the least element. -/
theorem neg_one_least {y : ℤ} (hy : y ≠ -1) : epsLt (fun _ => true) (-1) y := by
  refine ⟨Ne.symm hy, ?_⟩
  simp only [bitOne, iff_true]
  have hpos : (0 : ℤ) < 2 ^ padicValInt 2 (y - -1) := by positivity
  have h1 : (1 : ℤ) ≤ 2 ^ padicValInt 2 (y - -1) := by omega
  have : (-1 : ℤ) / 2 ^ padicValInt 2 (y - -1) = -1 :=
    (Int.ediv_eq_iff_of_pos hpos).2 ⟨by nlinarith, by nlinarith⟩
  rw [this]; rfl

/-- **Fixed-◁ dead end on ℤ**: there is no prefix-increasing chain of `◁`-safe words
exhausting ℤ. -/
theorem no_exhaustive_chain_twos_complement (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (fun _ => true)) (P n))
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x, ∃ n, x ∈ P n) : False :=
  no_exhaustive_safe_chain (epsLt_star' _) (fun _ hy => neg_one_least hy) P hsafe hpre hcov


/-! ## Strict total order and no endpoints -/

lemma dvd_of_le_val {d : ℤ} {n : ℕ} (h : n ≤ padicValInt 2 d) : (2 : ℤ) ^ n ∣ d :=
  (pow_dvd_pow 2 h).trans (two_pow_val_dvd d)

lemma le_val_of_dvd {d : ℤ} (hd : d ≠ 0) {n : ℕ} (h : (2 : ℤ) ^ n ∣ d) : n ≤ padicValInt 2 d := by
  have h' : ((2 : ℕ) : ℤ) ^ n ∣ d := by exact_mod_cast h
  rcases (padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) n d).1 h' with h0 | h0
  · exact absurd h0 hd
  · exact h0

/-- If `2^(j+1) ∣ y - x` then `x` and `y` have the same digit at position `j`. -/
lemma digit_eq_of_dvd {x y : ℤ} {j : ℕ} (h : (2 : ℤ) ^ (j + 1) ∣ y - x) :
    x / 2 ^ j % 2 = y / 2 ^ j % 2 := by
  obtain ⟨t, ht⟩ := h
  have hy : y = x + (2 * t) * 2 ^ j := by rw [pow_succ] at ht; linarith
  have h0 : (2 : ℤ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hy, Int.add_mul_ediv_right _ _ h0]
  omega

/-- At `k = ν₂(y - x)` the digits of `x` and `y` differ. -/
lemma digit_ne {x y : ℤ} (hne : x ≠ y) :
    (y / 2 ^ padicValInt 2 (y - x) % 2 = 1 ↔ ¬ x / 2 ^ padicValInt 2 (y - x) % 2 = 1) := by
  have hr : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hq := odd_part (y - x) hr
  have hy := div_pow_add_mul x (y - x) 1
  rw [show x + 1 * (y - x) = y by ring, one_mul] at hy
  rw [hy]
  omega

theorem epsLt_trans (ε : ℕ → Bool) {x y z : ℤ} (h1 : epsLt ε x y) (h2 : epsLt ε y z) :
    epsLt ε x z := by
  obtain ⟨hxy, c1⟩ := h1
  obtain ⟨hyz, c2⟩ := h2
  unfold bitOne at c1 c2
  have d1 : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have d2 : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
  set k1 := padicValInt 2 (y - x) with hk1
  set k2 := padicValInt 2 (z - y) with hk2
  have nd1 : ¬ (2 : ℤ) ^ (k1 + 1) ∣ y - x := fun h => by
    have := le_val_of_dvd d1 h; omega
  have nd2 : ¬ (2 : ℤ) ^ (k2 + 1) ∣ z - y := fun h => by
    have := le_val_of_dvd d2 h; omega
  have e : z - x = (y - x) + (z - y) := by ring
  rcases lt_trichotomy k1 k2 with hlt | heq | hgt
  · -- the first difference is at k1
    have hd2 : (2 : ℤ) ^ (k1 + 1) ∣ z - y := dvd_of_le_val (by omega)
    have hd1 : (2 : ℤ) ^ k1 ∣ y - x := two_pow_val_dvd _
    have hd2' : (2 : ℤ) ^ k1 ∣ z - y := (pow_dvd_pow 2 (Nat.le_succ k1)).trans hd2
    have hxz : z - x ≠ 0 := by
      intro h0; apply nd1
      have : y - x = -(z - y) := by linarith
      rw [this]; exact (dvd_neg).2 hd2
    have hk3 : padicValInt 2 (z - x) = k1 := by
      apply le_antisymm
      · by_contra hc
        apply nd1
        have := dvd_of_le_val (d := z - x) (n := k1 + 1) (by omega)
        have : y - x = (z - x) - (z - y) := by ring
        rw [this]; exact dvd_sub ‹_› hd2
      · exact le_val_of_dvd hxz (by rw [e]; exact dvd_add hd1 hd2')
    refine ⟨fun h => hxz (by rw [h]; ring), ?_⟩
    unfold bitOne
    rw [hk3]; exact c1
  · -- same level: contradiction
    exfalso
    have dn := digit_ne hxy
    rw [← hk1] at dn
    rw [← heq] at c2
    tauto
  · -- the first difference is at k2; x and y agree there
    have hd1 : (2 : ℤ) ^ (k2 + 1) ∣ y - x := dvd_of_le_val (by omega)
    have hd2 : (2 : ℤ) ^ k2 ∣ z - y := two_pow_val_dvd _
    have hd1' : (2 : ℤ) ^ k2 ∣ y - x := (pow_dvd_pow 2 (Nat.le_succ k2)).trans hd1
    have hxz : z - x ≠ 0 := by
      intro h0; apply nd2
      have : z - y = -(y - x) := by linarith
      rw [this]; exact (dvd_neg).2 hd1
    have hk3 : padicValInt 2 (z - x) = k2 := by
      apply le_antisymm
      · by_contra hc
        apply nd2
        have := dvd_of_le_val (d := z - x) (n := k2 + 1) (by omega)
        have : z - y = (z - x) - (y - x) := by ring
        rw [this]; exact dvd_sub ‹_› hd1
      · exact le_val_of_dvd hxz (by rw [e]; exact dvd_add hd1' hd2)
    refine ⟨fun h => hxz (by rw [h]; ring), ?_⟩
    unfold bitOne
    rw [hk3, digit_eq_of_dvd hd1]; exact c2

theorem epsLt_total (ε : ℕ → Bool) {x y : ℤ} (hne : x ≠ y) : epsLt ε x y ∨ epsLt ε y x := by
  by_cases h : (bitOne x (padicValInt 2 (y - x)) ↔ ε (padicValInt 2 (y - x)) = true)
  · exact Or.inl ⟨hne, h⟩
  · right
    refine ⟨Ne.symm hne, ?_⟩
    rw [padicValInt_sub_comm]
    have dn := digit_ne hne
    unfold bitOne at h ⊢
    tauto

theorem epsLt_isStrictTotalOrder' (ε : ℕ → Bool) : IsStrictTotalOrder ℤ (epsLt ε) where
  trichotomous a b h1 h2 := by
    by_contra hne
    rcases epsLt_total ε hne with h | h
    · exact h1 h
    · exact h2 h
  irrefl a h := h.1 rfl
  trans a b c h1 h2 := epsLt_trans ε h1 h2

/-- Digits of an integer are eventually constant: `1` for negatives, `0` otherwise. -/
lemma digit_eventually (x : ℤ) {n : ℕ} (hn : x.natAbs ≤ n) :
    (x / 2 ^ n % 2 = 1 ↔ x < 0) := by
  have hlt : (x.natAbs : ℤ) < 2 ^ n := by exact_mod_cast lt_of_le_of_lt hn n.lt_two_pow_self
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  rcases lt_or_ge x 0 with hx | hx
  · have : x / 2 ^ n = -1 := (Int.ediv_eq_iff_of_pos hpos).2 ⟨by omega, by omega⟩
    rw [this]; simp [hx]
  · have : x / 2 ^ n = 0 := Int.ediv_eq_zero_of_lt hx (by omega)
    rw [this]; simp; omega

theorem epsLt_no_endpoints' (ε : ℕ → Bool) (hε : ¬ ∃ N : ℕ, ∃ b : Bool, ∀ n ≥ N, ε n = b)
    (x : ℤ) : (∃ y, epsLt ε y x) ∧ (∃ y, epsLt ε x y) := by
  have key : ∀ b : Bool, ∃ n, x.natAbs ≤ n ∧ ε n ≠ b := by
    intro b
    by_contra hc
    push Not at hc
    exact hε ⟨x.natAbs, b, fun n hn => hc n hn⟩
  -- flipping the digit at a level `n` where `x` is "wrong"/"right"
  have flip : ∀ n : ℕ, x.natAbs ≤ n → ∃ y, y ≠ x ∧ padicValInt 2 (y - x) = n ∧
      (y / 2 ^ n % 2 = 1 ↔ ¬ x / 2 ^ n % 2 = 1) := by
    intro n hn
    refine ⟨x + 2 ^ n, ?_, ?_, ?_⟩
    · have : (0 : ℤ) < 2 ^ n := by positivity
      omega
    · have hne : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [show x + 2 ^ n - x = 2 ^ n by ring]
      apply le_antisymm
      · by_contra hc
        have hd := dvd_of_le_val (d := (2 : ℤ) ^ n) (n := n + 1) (by omega)
        have hp : (0 : ℤ) < 2 ^ n := by positivity
        have := Int.le_of_dvd hp hd
        rw [pow_succ] at this
        linarith
      · exact le_val_of_dvd hne dvd_rfl
    · have h0 : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [show x + 2 ^ n = x + 1 * 2 ^ n by ring, Int.add_mul_ediv_right _ _ h0]
      omega
  constructor
  · obtain ⟨n, hn, hb⟩ := key (decide (x < 0))
    obtain ⟨y, hyx, hv, hd⟩ := flip n hn
    refine ⟨y, hyx, ?_⟩
    rw [padicValInt_sub_comm, hv]
    unfold bitOne
    have := digit_eventually x hn
    cases h : ε n <;> simp_all
  · obtain ⟨n, hn, hb⟩ := key (!decide (x < 0))
    obtain ⟨y, hyx, hv, hd⟩ := flip n hn
    refine ⟨y, Ne.symm hyx, ?_⟩
    rw [hv]
    unfold bitOne
    have := digit_eventually x hn
    cases h : ε n <;> simp_all

/-- List version of an arithmetic progression of length `l` with first term `a` and difference
`d`, listed either forwards or backwards (formal-conjectures `List.IsAPOfLengthWith`). -/
def ListIsAPOfLengthWith {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

/-- `s` is an arithmetic progression of length `l` (formal-conjectures `List.IsAPOfLength`). -/
def ListIsAPOfLength {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, ListIsAPOfLengthWith s l a d

/-- `f` has a monotone `k`-term AP: indices `b₁ < ⋯ < b_k` with `f b₁, …, f b_k` an increasing or
decreasing AP (formal-conjectures `HasMonotoneAP`). -/
def HasMonotoneAP {α β : Type*} [AddCommMonoid α] [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

theorem hasAP4_of' (f : ℕ → ℤ) (i j k l : ℕ) (a d : ℤ) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : f i = a) (hj : f j = a + d) (hk : f k = a + 2 * d) (hl : f l = a + 3 * d) :
    HasMonotoneAP f 4 := by
  refine ⟨[i, j, k, l], ⟨a, d, Or.inl ?_⟩, ?_⟩
  · simp [List.range_succ, hi, hj, hk, hl]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, hkl, fun _ h => h.elim⟩

theorem mem_pref (f : ℕ ≃ ℤ) (N : ℕ) (x : ℤ) :
    x ∈ (List.range N).map f ↔ f.symm x < N := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa using hi
  · intro h; exact ⟨f.symm x, h, by simp⟩

theorem idx_pref (f : ℕ ≃ ℤ) (N : ℕ) (x : ℤ) (h : f.symm x < N) :
    ((List.range N).map f).idxOf x = f.symm x := by
  have hnd : ((List.range N).map f).Nodup := List.Nodup.map f.injective List.nodup_range
  have hlen : f.symm x < ((List.range N).map f).length := by simpa using h
  have hget : ((List.range N).map f)[f.symm x]'hlen = x := by simp
  have := List.Nodup.idxOf_getElem hnd (f.symm x) hlen
  rw [hget] at this
  exact this

theorem compLt_pref (R : ℤ → ℤ → Prop) (f : ℕ ≃ ℤ) (N : ℕ) (x y : ℤ) :
    compLt R ((List.range N).map f) x y ↔
      (f.symm x < N ∧ f.symm y < N ∧ f.symm x < f.symm y) ∨ (f.symm x < N ∧ N ≤ f.symm y) ∨
      (N ≤ f.symm x ∧ N ≤ f.symm y ∧ R x y) := by
  unfold compLt
  simp only [mem_pref, not_lt]
  constructor
  · rintro (⟨h1, h2, h3⟩ | h | h)
    · rw [idx_pref f N x h1, idx_pref f N y h2] at h3; exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨h1, h2, h3⟩ | h | h)
    · refine Or.inl ⟨h1, h2, ?_⟩; rw [idx_pref f N x h1, idx_pref f N y h2]; exact h3
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **Safe prefixes of a 4AP-free permutation ("closed cuts").** Let `R` be a relation on `ℤ` with
no monotone 3-AP and Ho's property (*), and let `f : ℕ ≃ ℤ` have no monotone 4-AP. Then the
prefix `f 0, …, f (N-1)` is an `R`-safe word iff the cut at `N` is `R`-closed: whenever `i < j < N`,
`R (f i) (f j)` and `2 f j - f i` occurs at a position `≥ N`, the value `3 f j - 2 f i` occurs
at a position `< N`. Hence a Ho-type construction (prefix chain of `R`-safe words exhausting `ℤ`)
is the same thing as a 4AP-free permutation with infinitely many `R`-closed cuts. -/
theorem prefix_safe_iff_closed_cut (R : ℤ → ℤ → Prop) (hA : No3AP R) (hB : Star R)
    (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ) :
    Safe R ((List.range N).map f) ↔
      ∀ i j : ℕ, i < j → j < N → R (f i) (f j) → N ≤ f.symm (2 * f j - f i) →
        f.symm (3 * f j - 2 * f i) < N := by
  constructor
  · intro hS i j hij hjN hR h2
    by_contra h3
    push Not at h3
    have hne : f j - f i ≠ 0 := by
      intro h; have := f.injective (show f j = f i by linarith); omega
    apply hS (f i) (f j - f i) hne
    have e1 : f i + (f j - f i) = f j := by ring
    have e2 : f i + 2 * (f j - f i) = 2 * f j - f i := by ring
    have e3 : f i + 3 * (f j - f i) = 3 * f j - 2 * f i := by ring
    rw [e1, e2, e3, compLt_pref, compLt_pref, compLt_pref]
    simp only [Equiv.symm_apply_apply]
    refine ⟨Or.inl ⟨by omega, hjN, hij⟩, Or.inr (Or.inl ⟨hjN, h2⟩), Or.inr (Or.inr ⟨h2, h3, ?_⟩)⟩
    have := (hB (f i) (f j - f i) hne).1
    rw [e1, e2, e3] at this
    exact this hR
  · intro H a r hr ⟨h1, h2, h3⟩
    rw [compLt_pref] at h1 h2 h3
    set p0 := f.symm a with hp0
    set p1 := f.symm (a + r) with hp1
    set p2 := f.symm (a + 2 * r) with hp2
    set p3 := f.symm (a + 3 * r) with hp3
    have f0 : f p0 = a := by simp [hp0]
    have f1 : f p1 = a + r := by simp [hp1]
    have f2 : f p2 = a + 2 * r := by simp [hp2]
    have f3 : f p3 = a + 3 * r := by simp [hp3]
    have ap : ∀ (_ : p0 < p1) (_ : p1 < p2) (_ : p2 < p3), False := fun q1 q2 q3 =>
      hf (hasAP4_of' f p0 p1 p2 p3 a r q1 q2 q3 f0 f1 f2 f3)
    rcases h1 with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩
    · rcases h2 with ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · rcases h3 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3⟩
        · exact ap a3 b3 c3
        · exact ap a3 b3 (by omega)
        · omega
      · rcases h3 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3⟩
        · omega
        · omega
        · have hR : R (f p0) (f p1) := by
            rw [f0, f1]
            have := (hB a r hr).2 c3
            exact this
          have hq2 : f.symm (2 * f p1 - f p0) = p2 := by
            rw [f0, f1, hp2]; congr 1; ring
          have hq3 : f.symm (3 * f p1 - 2 * f p0) = p3 := by
            rw [f0, f1, hp3]; congr 1; ring
          have := H p0 p1 a3 b1 hR (by rw [hq2]; exact b2)
          rw [hq3] at this
          omega
      · omega
    · rcases h2 with ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · omega
      · omega
      · rcases h3 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3⟩
        · omega
        · omega
        · apply hA (a + r) r hr
          have e1 : a + r + r = a + 2 * r := by ring
          have e2 : a + r + 2 * r = a + 3 * r := by ring
          rw [e1, e2]
          exact ⟨b3, c3⟩
    · rcases h2 with ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · omega
      · omega
      · exact hA a r hr ⟨a3, b3⟩

/-! ## Session 44: stage-dependent ε — eliminating the order -/

/-- In an ε-order, `b ≺ a` is decided by `ε` at `ν₂(b - a)` and the digit of `b` there. -/
lemma epsLt_rev_iff (ε : ℕ → Bool) {a b : ℤ} (hne : a ≠ b) :
    epsLt ε b a ↔ (bitOne b (padicValInt 2 (b - a)) ↔ ε (padicValInt 2 (b - a)) = true) := by
  unfold epsLt
  rw [padicValInt_sub_comm a b]
  exact ⟨fun h => h.2, fun h => ⟨Ne.symm hne, h⟩⟩

/-- **Per-ε closed cuts, order-free form.** For a 4AP-free `f : ℕ ≃ ℤ`, the prefix of length `N`
is `epsLt ε`-safe iff for every "open pair" `i < j < N` (both `2 f j - f i` and `3 f j - 2 f i`
placed at positions `≥ N`), the digit of `f j` at `k = ν₂(f j - f i)` is `1` exactly when `ε k`. -/
theorem eps_safe_prefix_iff_open_pairs (ε : ℕ → Bool) (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4)
    (N : ℕ) :
    Safe (epsLt ε) ((List.range N).map f) ↔
      ∀ i j : ℕ, i < j → j < N → N ≤ f.symm (2 * f j - f i) → N ≤ f.symm (3 * f j - 2 * f i) →
        (bitOne (f j) (padicValInt 2 (f j - f i)) ↔ ε (padicValInt 2 (f j - f i)) = true) := by
  rw [prefix_safe_iff_closed_cut _ (epsLt_no3AP ε) (epsLt_star' ε) f hf N]
  have hne : ∀ i j : ℕ, i < j → f i ≠ f j := fun i j hij h => by
    have := f.injective h; omega
  constructor
  · intro H i j hij hjN h2 h3
    rw [← epsLt_rev_iff ε (hne i j hij)]
    rcases epsLt_total ε (hne i j hij) with h | h
    · have := H i j hij hjN h h2; omega
    · exact h
  · intro H i j hij hjN hR h2
    by_contra h3
    push Not at h3
    have := (epsLt_rev_iff ε (hne i j hij)).2 (H i j hij hjN h2 h3)
    exact epsLt_asymm ε hR this

/-- **Stage-dependent ε, order eliminated.** For a 4AP-free `f : ℕ ≃ ℤ` and a cut `N`, some
ε-order makes the prefix `f 0, …, f (N-1)` safe iff the open pairs at `N` impose consistent digit
constraints: any two open pairs `(i, j)`, `(i', j')` (`i < j < N`, `2 f j - f i` and
`3 f j - 2 f i` both at positions `≥ N`) with the same `ν₂(f j - f i) = ν₂(f j' - f i') = k` have
`f j` and `f j'` with the same `k`-th binary digit. Hence a Ho-type chain with stage-dependent ε
exhausting ℤ is exactly a 4AP-free permutation of ℤ with infinitely many such consistent cuts. -/
theorem exists_eps_safe_prefix_iff (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ) :
    (∃ ε : ℕ → Bool, Safe (epsLt ε) ((List.range N).map f)) ↔
      ∀ i j i' j' : ℕ, i < j → j < N → N ≤ f.symm (2 * f j - f i) →
        N ≤ f.symm (3 * f j - 2 * f i) →
        i' < j' → j' < N → N ≤ f.symm (2 * f j' - f i') → N ≤ f.symm (3 * f j' - 2 * f i') →
        padicValInt 2 (f j - f i) = padicValInt 2 (f j' - f i') →
        (bitOne (f j) (padicValInt 2 (f j - f i)) ↔
          bitOne (f j') (padicValInt 2 (f j' - f i'))) := by
  constructor
  · rintro ⟨ε, hε⟩ i j i' j' hij hjN h2 h3 hij' hjN' h2' h3' hv
    rw [eps_safe_prefix_iff_open_pairs ε f hf N] at hε
    have A := hε i j hij hjN h2 h3
    have B := hε i' j' hij' hjN' h2' h3'
    rw [hv] at A
    rw [hv]
    exact A.trans B.symm
  · intro H
    classical
    let Op : ℕ → ℕ × ℕ → Prop := fun k p =>
      p.1 < p.2 ∧ p.2 < N ∧ N ≤ f.symm (2 * f p.2 - f p.1) ∧ N ≤ f.symm (3 * f p.2 - 2 * f p.1) ∧
        padicValInt 2 (f p.2 - f p.1) = k
    let ε : ℕ → Bool := fun k =>
      if h : ∃ p, Op k p then decide (bitOne (f h.choose.2) k) else true
    refine ⟨ε, (eps_safe_prefix_iff_open_pairs ε f hf N).2 ?_⟩
    intro i j hij hjN h2 h3
    have hex : ∃ p, Op (padicValInt 2 (f j - f i)) p := ⟨(i, j), hij, hjN, h2, h3, rfl⟩
    have hs := hex.choose_spec
    obtain ⟨q1, q2, q3, q4, q5⟩ := hs
    have key := H i j _ _ hij hjN h2 h3 q1 q2 q3 q4 q5.symm
    rw [q5] at key
    have hε : ε (padicValInt 2 (f j - f i)) =
        decide (bitOne (f hex.choose.2) (padicValInt 2 (f j - f i))) := by
      simp only [ε]; rw [dif_pos hex]
    rw [hε, decide_eq_true_eq]
    exact key


/-! ## Session 45: no two chained open pairs with equal valuation -/

/-- **Chained open pairs.** At a cut `N` of a 4AP-free `f : ℕ ≃ ℤ` which is safe for some
ε-order, two open pairs `(a, b)`, `(b, c)` sharing the middle position `b` never have the same
2-adic valuation `ν₂(f b - f a) = ν₂(f c - f b)`. -/
theorem open_chain_val_ne (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ)
    (hε : ∃ ε : ℕ → Bool, Safe (epsLt ε) ((List.range N).map f)) (a b c : ℕ)
    (hab : a < b) (hbc : b < c) (hcN : c < N)
    (h1 : N ≤ f.symm (2 * f b - f a)) (h2 : N ≤ f.symm (3 * f b - 2 * f a))
    (h3 : N ≤ f.symm (2 * f c - f b)) (h4 : N ≤ f.symm (3 * f c - 2 * f b)) :
    padicValInt 2 (f b - f a) ≠ padicValInt 2 (f c - f b) := by
  intro hv
  have H := (exists_eps_safe_prefix_iff f hf N).1 hε a b b c hab (by omega) h1 h2 hbc hcN h3 h4 hv
  have hne : f b ≠ f c := fun h => by have := f.injective h; omega
  have hd := digit_ne hne
  unfold bitOne at H
  rw [hv] at H
  tauto

lemma pos_ge_of_gt (f : ℕ ≃ ℤ) (N j : ℕ) (hmax : ∀ t < N, f t ≤ f j) (x : ℤ) (hx : f j < x) :
    N ≤ f.symm x := by
  by_contra h
  push Not at h
  have := hmax _ h
  rw [Equiv.apply_symm_apply] at this
  omega

lemma pos_ge_of_lt (f : ℕ ≃ ℤ) (N j : ℕ) (hmin : ∀ t < N, f j ≤ f t) (x : ℤ) (hx : x < f j) :
    N ≤ f.symm x := by
  by_contra h
  push Not at h
  have := hmin _ h
  rw [Equiv.apply_symm_apply] at this
  omega

/-- **Extremes obstruction for stage-dependent ε-chains.** Let `f : ℕ ≃ ℤ` be 4AP-free and let the
prefix `f 0, …, f (N-1)` be safe for some ε-order. Let positions `i < j < N` carry the two
extremes of the prefix (min and max, in either order), and put `k₀ = ν₂(f j - f i)`. Then no
element placed before the earlier extreme `f i` satisfies `ν₂(f i - f a) = k₀`
(equivalently, `f a ≢ f j (mod 2^(k₀+1))`). -/
theorem extremes_val_ne (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ)
    (hε : ∃ ε : ℕ → Bool, Safe (epsLt ε) ((List.range N).map f)) (i j : ℕ)
    (hij : i < j) (hjN : j < N)
    (hext : (∀ t < N, f i ≤ f t ∧ f t ≤ f j) ∨ (∀ t < N, f j ≤ f t ∧ f t ≤ f i))
    (a : ℕ) (hai : a < i) :
    padicValInt 2 (f i - f a) ≠ padicValInt 2 (f j - f i) := by
  have hne : ∀ p q : ℕ, p < q → f p ≠ f q := fun p q hpq h => by
    have := f.injective h; omega
  have hia := hne a i hai
  have hij' := hne i j hij
  refine open_chain_val_ne f hf N hε a i j hai hij hjN ?_ ?_ ?_ ?_
  · rcases hext with h | h
    · have := (h a (by omega)).1
      exact pos_ge_of_lt f N i (fun t ht => (h t ht).1) _ (by omega)
    · have := (h a (by omega)).2
      exact pos_ge_of_gt f N i (fun t ht => (h t ht).2) _ (by omega)
  · rcases hext with h | h
    · have := (h a (by omega)).1
      exact pos_ge_of_lt f N i (fun t ht => (h t ht).1) _ (by omega)
    · have := (h a (by omega)).2
      exact pos_ge_of_gt f N i (fun t ht => (h t ht).2) _ (by omega)
  · rcases hext with h | h
    · have := (h i (by omega)).2
      exact pos_ge_of_gt f N j (fun t ht => (h t ht).2) _ (by omega)
    · have := (h i (by omega)).1
      exact pos_ge_of_lt f N j (fun t ht => (h t ht).1) _ (by omega)
  · rcases hext with h | h
    · have := (h i (by omega)).2
      exact pos_ge_of_gt f N j (fun t ht => (h t ht).2) _ (by omega)
    · have := (h i (by omega)).1
      exact pos_ge_of_lt f N j (fun t ht => (h t ht).1) _ (by omega)

end E195Aux



open Erdos195 in
theorem solution (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ)
    (hε : ∃ ε : ℕ → Bool, Safe (epsLt ε) ((List.range N).map f)) (i j : ℕ)
    (hij : i < j) (hjN : j < N)
    (hext : (∀ t < N, f i ≤ f t ∧ f t ≤ f j) ∨ (∀ t < N, f j ≤ f t ∧ f t ≤ f i))
    (a : ℕ) (hai : a < i) :
    padicValInt 2 (f i - f a) ≠ padicValInt 2 (f j - f i) :=
  E195Aux.extremes_val_ne f hf N hε i j hij hjN hext a hai
