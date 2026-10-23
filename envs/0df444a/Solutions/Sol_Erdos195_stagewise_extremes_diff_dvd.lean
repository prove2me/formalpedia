-- Prove2me | solution 1 for Erdos195.stagewise_extremes_diff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T01:38:31.467259+00:00
-- url     : https://prove2.me/submissions/49ed3a7d-b32c-440d-8b84-1c68765b14d1

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

theorem record_not_above {R : ℤ → ℤ → Prop} (hB : Star R) {P : List ℤ} (hS : Safe R P)
    {a M : ℤ} (haP : a ∈ P) (hMP : M ∈ P) (haM : P.idxOf a < P.idxOf M)
    (hext : (∀ x ∈ P, x ≤ M) ∨ (∀ x ∈ P, M ≤ x)) : ¬ R a M := by
  intro hRaM
  have hMa : M ≠ a := by rintro rfl; exact lt_irrefl _ haM
  have hr : M - a ≠ 0 := sub_ne_zero.mpr hMa
  have e1 : a + (M - a) = M := by ring
  have hout : a + 2 * (M - a) ∉ P ∧ a + 3 * (M - a) ∉ P := by
    rcases hext with h | h
    · have hle := h a haP
      have hlt : a < M := lt_of_le_of_ne hle (Ne.symm hMa)
      constructor <;> intro hm <;> have := h _ hm <;> linarith
    · have hle := h a haP
      have hlt : M < a := lt_of_le_of_ne hle hMa
      constructor <;> intro hm <;> have := h _ hm <;> linarith
  have hR : R (a + 2 * (M - a)) (a + 3 * (M - a)) := by
    have := (hB a (M - a) hr).1
    rw [e1] at this
    exact this hRaM
  apply hS a (M - a) hr
  rw [e1]
  exact ⟨Or.inl ⟨haP, hMP, haM⟩, Or.inr (Or.inl ⟨hMP, hout.1⟩),
    Or.inr (Or.inr ⟨hout.1, hout.2, hR⟩)⟩

/-- If `x ∈ P m`, `P m` is a prefix of `P n`, `M ∈ P n` and `M ∉ P m`, then `x` comes before `M`
in `P n`. -/
lemma idx_lt_of_prefix {Pm Pn : List ℤ} (hp : Pm <+: Pn) {x M : ℤ} (hx : x ∈ Pm) (hM : M ∉ Pm) :
    Pn.idxOf x < Pn.idxOf M := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.idxOf_append, List.idxOf_append, if_pos hx, if_neg hM]
  have := List.idxOf_lt_length_of_mem hx
  omega

/-- **Chain corollary.** Let `R` satisfy (*) and let `P 0 ⊑ P 1 ⊑ ⋯` be a prefix-increasing chain
of safe words whose union is ℤ. Then for every `x` there is `N` such that for all `n ≥ N`, the
maximum `M` and the minimum `m` of `P n` satisfy `¬ R x M` and `¬ R x m`
(for a strict total order: `M` and `m` lie strictly `R`-below `x`, or equal it). -/
theorem chain_extremes_not_above {R : ℤ → ℤ → Prop} (hB : Star R) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe R (P n)) (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x, ∃ n, x ∈ P n)
    (x : ℤ) : ∃ N, ∀ n ≥ N, ∀ M ∈ P n,
      ((∀ y ∈ P n, y ≤ M) → ¬ R x M) ∧ ((∀ y ∈ P n, M ≤ y) → ¬ R x M) := by
  obtain ⟨n0, hx0⟩ := hcov x
  have hne0 : (P n0).toFinset.Nonempty := ⟨x, List.mem_toFinset.2 hx0⟩
  set b := (P n0).toFinset.max' hne0 with hb
  set c := (P n0).toFinset.min' hne0 with hc
  obtain ⟨n1, h1⟩ := hcov (b + 1)
  obtain ⟨n2, h2⟩ := hcov (c - 1)
  refine ⟨max n0 (max n1 n2), fun n hn M hMP => ?_⟩
  have hn0 : n0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hp := prefix_mono hpre hn0
  have hxn : x ∈ P n := hp.subset hx0
  have hb1 : b + 1 ∈ P n := (prefix_mono hpre hn1).subset h1
  have hc1 : c - 1 ∈ P n := (prefix_mono hpre hn2).subset h2
  have hbmax : ∀ y ∈ P n0, y ≤ b := fun y hy => Finset.le_max' _ y (List.mem_toFinset.2 hy)
  have hcmin : ∀ y ∈ P n0, c ≤ y := fun y hy => Finset.min'_le _ y (List.mem_toFinset.2 hy)
  constructor
  · intro hmax
    have hbM : b < M := by have := hmax _ hb1; linarith
    have hM0 : M ∉ P n0 := fun h => by have := hbmax _ h; linarith
    exact record_not_above hB (hsafe n) hxn hMP (idx_lt_of_prefix hp hx0 hM0) (Or.inl hmax)
  · intro hmin
    have hcM : M < c := by have := hmin _ hc1; linarith
    have hM0 : M ∉ P n0 := fun h => by have := hcmin _ h; linarith
    exact record_not_above hB (hsafe n) hxn hMP (idx_lt_of_prefix hp hx0 hM0) (Or.inr hmin)


/-! ## Eventual congruence of stage extrema (2-adic convergence to ξ_ε) -/

/-- Partial sums `e ε k = Σ_{j<k} ε_j 2^j`. -/
def ePart (ε : ℕ → Bool) : ℕ → ℤ
  | 0 => 0
  | k + 1 => ePart ε k + (if ε k then 2 ^ k else 0)

lemma ePart_bounds (ε : ℕ → Bool) (k : ℕ) : 0 ≤ ePart ε k ∧ ePart ε k < 2 ^ k := by
  induction k with
  | zero => simp [ePart]
  | succ k ih =>
    simp only [ePart, pow_succ]
    split_ifs <;> constructor <;> linarith [ih.1, ih.2]

lemma ePart_dvd_sub (ε : ℕ → Bool) {m k : ℕ} (h : m ≤ k) :
    (2 : ℤ) ^ m ∣ ePart ε k - ePart ε m := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    have : ePart ε (k + 1) - ePart ε m = (ePart ε k - ePart ε m) + (if ε k then 2 ^ k else 0) := by
      simp only [ePart]; ring
    rw [this]
    refine dvd_add ih ?_
    split_ifs
    · exact pow_dvd_pow 2 hmk
    · exact dvd_zero _

/-- The `j`-th digit of `e ε k` is `ε j` for `j < k`. -/
lemma ePart_digit (ε : ℕ → Bool) {j k : ℕ} (hjk : j < k) :
    (bitOne (ePart ε k) j ↔ ε j = true) := by
  unfold bitOne
  have hd := ePart_dvd_sub ε (show j + 1 ≤ k by omega)
  rw [← digit_eq_of_dvd hd]
  have hb := ePart_bounds ε j
  have hp : (0 : ℤ) < 2 ^ j := by positivity
  have h0 : (2 : ℤ) ^ j ≠ 0 := ne_of_gt hp
  simp only [ePart]
  cases hε : ε j
  · simp only [Bool.false_eq_true, if_false, add_zero]
    rw [Int.ediv_eq_zero_of_lt hb.1 hb.2]; simp
  · simp only [if_true]
    have : (ePart ε j + 2 ^ j) / 2 ^ j = 1 := by
      rw [show ePart ε j + 2 ^ j = ePart ε j + 1 * 2 ^ j by ring, Int.add_mul_ediv_right _ _ h0,
        Int.ediv_eq_zero_of_lt hb.1 hb.2]; simp
    rw [this]; simp

/-- **Key digit lemma.** If `x` is `≺_ε`-below `e ε k`, then `x ≡ e ε k (mod 2^k)`. -/
theorem dvd_of_epsLt_ePart (ε : ℕ → Bool) (k : ℕ) {x : ℤ} (h : epsLt ε x (ePart ε k)) :
    (2 : ℤ) ^ k ∣ x - ePart ε k := by
  by_contra hnd
  obtain ⟨hne, hiff⟩ := h
  set j := padicValInt 2 (ePart ε k - x) with hj
  have hr : ePart ε k - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hjk : j < k := by
    by_contra hc
    apply hnd
    have := dvd_of_le_val (d := ePart ε k - x) (n := k) (by omega)
    rw [show x - ePart ε k = -(ePart ε k - x) by ring]
    exact dvd_neg.mpr this
  have hdig := ePart_digit ε hjk
  have dn := digit_ne hne
  unfold bitOne at hiff hdig
  rw [← hj] at dn
  tauto

/-- **Eventual congruence of stage extrema.** Let `P 0 ⊑ P 1 ⊑ ⋯` be a prefix-increasing chain of
`≺_ε`-safe words whose union is ℤ. Then for every `k` there is `N` such that for all `n ≥ N`,
the maximum and the minimum of `P n` are both `≡ e ε k = Σ_{j<k} ε_j 2^j (mod 2^k)`. -/
theorem chain_extremes_congr (ε : ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt ε) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ M ∈ P n, ((∀ y ∈ P n, y ≤ M) ∨ (∀ y ∈ P n, M ≤ y)) →
      (2 : ℤ) ^ k ∣ M - ePart ε k := by
  obtain ⟨N, hN⟩ := chain_extremes_not_above (epsLt_star' ε) P hsafe hpre hcov (ePart ε k)
  refine ⟨N, fun n hn M hM hext => ?_⟩
  have hnot : ¬ epsLt ε (ePart ε k) M := by
    rcases hext with h | h
    · exact (hN n hn M hM).1 h
    · exact (hN n hn M hM).2 h
  by_cases heq : M = ePart ε k
  · rw [heq, sub_self]; exact dvd_zero _
  · rcases epsLt_total ε heq with h | h
    · exact dvd_of_epsLt_ePart ε k h
    · exact absurd h hnot

lemma ePart_eq_sum (ε : ℕ → Bool) (k : ℕ) :
    ePart ε k = ∑ j ∈ Finset.range k, (if ε j then (2 : ℤ) ^ j else 0) := by
  induction k with
  | zero => simp [ePart]
  | succ k ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- Statement form with the partial sum written out. -/
theorem epsLt_chain_extremes_congr (ε : ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt ε) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ M ∈ P n, ((∀ y ∈ P n, y ≤ M) ∨ (∀ y ∈ P n, M ≤ y)) →
      (2 : ℤ) ^ k ∣ M - ∑ j ∈ Finset.range k, (if ε j then (2 : ℤ) ^ j else 0) := by
  rw [← ePart_eq_sum]
  exact chain_extremes_congr ε P hsafe hpre hcov k


/-! ## Stage-dependent completion orders -/

/-- Chain corollary with a completion order `R n` that may change from stage to stage. -/
theorem stagewise_extremes_not_above (R : ℕ → ℤ → ℤ → Prop) (hB : ∀ n, Star (R n))
    (P : ℕ → List ℤ) (hsafe : ∀ n, Safe (R n) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (x : ℤ) : ∃ N, ∀ n ≥ N, ∀ M ∈ P n,
      ((∀ y ∈ P n, y ≤ M) ∨ (∀ y ∈ P n, M ≤ y)) → ¬ R n x M := by
  obtain ⟨n0, hx0⟩ := hcov x
  have hne0 : (P n0).toFinset.Nonempty := ⟨x, List.mem_toFinset.2 hx0⟩
  set b := (P n0).toFinset.max' hne0 with hb
  set c := (P n0).toFinset.min' hne0 with hc
  obtain ⟨n1, h1⟩ := hcov (b + 1)
  obtain ⟨n2, h2⟩ := hcov (c - 1)
  refine ⟨max n0 (max n1 n2), fun n hn M hMP hext => ?_⟩
  have hn0 : n0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hp := prefix_mono hpre hn0
  have hxn : x ∈ P n := hp.subset hx0
  have hb1 : b + 1 ∈ P n := (prefix_mono hpre hn1).subset h1
  have hc1 : c - 1 ∈ P n := (prefix_mono hpre hn2).subset h2
  have hbmax : ∀ y ∈ P n0, y ≤ b := fun y hy => Finset.le_max' _ y (List.mem_toFinset.2 hy)
  have hcmin : ∀ y ∈ P n0, c ≤ y := fun y hy => Finset.min'_le _ y (List.mem_toFinset.2 hy)
  have hM0 : M ∉ P n0 := by
    rcases hext with hmax | hmin
    · have hbM : b < M := by have := hmax _ hb1; linarith
      exact fun h => by have := hbmax _ h; linarith
    · have hcM : M < c := by have := hmin _ hc1; linarith
      exact fun h => by have := hcmin _ h; linarith
  exact record_not_above (hB n) (hsafe n) hxn hMP (idx_lt_of_prefix hp hx0 hM0) hext

/-- **Stage-dependent eventual congruence.** Let `P 0 ⊑ P 1 ⊑ ⋯` be a prefix-increasing chain
whose union is ℤ, where each `P n` is safe for its *own* ε-order `ε n` (the order may change from
stage to stage). Then for every `k` there is `N` such that for all `n ≥ N` the maximum and the
minimum of `P n` are `≡ Σ_{j<k} (ε n j) 2^j (mod 2^k)`. -/
theorem stagewise_chain_extremes_congr (ε : ℕ → ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (ε n)) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ M ∈ P n, ((∀ y ∈ P n, y ≤ M) ∨ (∀ y ∈ P n, M ≤ y)) →
      (2 : ℤ) ^ k ∣ M - ePart (ε n) k := by
  have hN := fun x => stagewise_extremes_not_above (fun n => epsLt (ε n))
    (fun n => epsLt_star' (ε n)) P hsafe hpre hcov x
  choose N hN using hN
  set g : ℕ → ℕ := fun i => N (i : ℤ) with hg
  refine ⟨(Finset.range (2 ^ k)).sup g, fun n hn M hM hext => ?_⟩
  have hb := ePart_bounds (ε n) k
  set e := ePart (ε n) k with he
  have he' : (e.toNat : ℤ) = e := Int.toNat_of_nonneg hb.1
  have hmem : e.toNat ∈ Finset.range (2 ^ k) := by
    rw [Finset.mem_range]; zify; rw [he']; exact_mod_cast hb.2
  have hle : N (e.toNat : ℤ) ≤ n :=
    le_trans (Finset.le_sup (f := g) hmem) hn
  have hnot : ¬ epsLt (ε n) e M := by
    have := hN (e.toNat : ℤ) n hle M hM hext
    rwa [he'] at this
  by_cases heq : M = e
  · rw [heq, sub_self]; exact dvd_zero _
  · rcases epsLt_total (ε n) heq with h | h
    · exact dvd_of_epsLt_ePart (ε n) k h
    · exact absurd h hnot

/-- **Order-free corollary.** In any exhaustive prefix chain of words, each safe for some ε-order
(possibly different at every stage), the diameter `max P n - min P n` is eventually divisible by
every power of `2`. -/
theorem stagewise_extremes_diff_dvd (ε : ℕ → ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (ε n)) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ U ∈ P n, ∀ L ∈ P n, (∀ y ∈ P n, y ≤ U) → (∀ y ∈ P n, L ≤ y) →
      (2 : ℤ) ^ k ∣ U - L := by
  obtain ⟨N, hN⟩ := stagewise_chain_extremes_congr ε P hsafe hpre hcov k
  refine ⟨N, fun n hn U hU L hL hmax hmin => ?_⟩
  have h1 := hN n hn U hU (Or.inl hmax)
  have h2 := hN n hn L hL (Or.inr hmin)
  have := dvd_sub h1 h2
  rwa [show U - ePart (ε n) k - (L - ePart (ε n) k) = U - L by ring] at this

end E195Aux



open Erdos195 in
theorem solution (ε : ℕ → ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (ε n)) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ U ∈ P n, ∀ L ∈ P n, (∀ y ∈ P n, y ≤ U) → (∀ y ∈ P n, L ≤ y) →
      (2 : ℤ) ^ k ∣ U - L :=
  E195Aux.stagewise_extremes_diff_dvd ε P hsafe hpre hcov k
