-- Prove2me | solution 1 for Erdos195.epsLt_safe_append_far
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:22:16.857729+00:00
-- url     : https://prove2.me/submissions/11aee37b-3ca7-4661-9225-3a1ae3392631

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


def SafeConds (R : ℤ → ℤ → Prop) (P : List ℤ) : Prop :=
  (∀ a r : ℤ, r ≠ 0 → a ∈ P → a + r ∈ P → a + 2 * r ∈ P →
      P.idxOf a < P.idxOf (a + r) → P.idxOf (a + r) < P.idxOf (a + 2 * r) →
      a + 3 * r ∈ P ∧ ¬ P.idxOf (a + 2 * r) < P.idxOf (a + 3 * r)) ∧
  (∀ a r : ℤ, r ≠ 0 → a ∈ P → a + r ∈ P → P.idxOf a < P.idxOf (a + r) → R a (a + r) →
      a + 2 * r ∈ P ∨ a + 3 * r ∈ P)

theorem safe_iff_conds {R : ℤ → ℤ → Prop} (hA : No3AP R) (hB : Star R) (P : List ℤ) :
    Safe R P ↔ SafeConds R P := by
  constructor
  · intro hS
    refine ⟨fun a r hr h0 h1 h2 i01 i12 => ?_, fun a r hr h0 h1 i01 hR => ?_⟩
    · by_cases h3 : a + 3 * r ∈ P
      · refine ⟨h3, fun i23 => hS a r hr ⟨Or.inl ⟨h0, h1, i01⟩, Or.inl ⟨h1, h2, i12⟩,
          Or.inl ⟨h2, h3, i23⟩⟩⟩
      · exact absurd ⟨Or.inl ⟨h0, h1, i01⟩, Or.inl ⟨h1, h2, i12⟩, Or.inr (Or.inl ⟨h2, h3⟩)⟩
          (hS a r hr)
    · by_contra hc
      push_neg at hc
      exact hS a r hr ⟨Or.inl ⟨h0, h1, i01⟩, Or.inr (Or.inl ⟨h1, hc.1⟩),
        Or.inr (Or.inr ⟨hc.1, hc.2, (hB a r hr).1 hR⟩)⟩
  · rintro ⟨hi, hii⟩ a r hr ⟨c1, c2, c3⟩
    have e2 : a + r + r = a + 2 * r := by ring
    have e3 : a + r + 2 * r = a + 3 * r := by ring
    have hA' : ¬ (R (a + r) (a + 2 * r) ∧ R (a + 2 * r) (a + 3 * r)) := by
      have := hA (a + r) r hr; rw [e2, e3] at this; exact this
    rcases c1 with ⟨h0, h1, i01⟩ | ⟨h0, h1⟩ | ⟨h0, h1, R01⟩
    · rcases c2 with ⟨-, h2, i12⟩ | ⟨-, h2⟩ | ⟨h1', -⟩
      · obtain ⟨h3, n23⟩ := hi a r hr h0 h1 h2 i01 i12
        rcases c3 with ⟨-, -, i23⟩ | ⟨-, h3'⟩ | ⟨h2', -⟩
        · exact n23 i23
        · exact h3' h3
        · exact h2' h2
      · rcases c3 with ⟨h2', -⟩ | ⟨h2', -⟩ | ⟨-, h3, R23⟩
        · exact h2 h2'
        · exact h2 h2'
        · rcases hii a r hr h0 h1 i01 ((hB a r hr).2 R23) with h | h
          · exact h2 h
          · exact h3 h
      · exact h1' h1
    · rcases c2 with ⟨h1', -⟩ | ⟨h1', -⟩ | ⟨-, h2, R12⟩
      · exact h1 h1'
      · exact h1 h1'
      · rcases c3 with ⟨h2', -⟩ | ⟨h2', -⟩ | ⟨-, -, R23⟩
        · exact h2 h2'
        · exact h2 h2'
        · exact hA' ⟨R12, R23⟩
    · rcases c2 with ⟨h1', -⟩ | ⟨h1', -⟩ | ⟨-, -, R12⟩
      · exact h1 h1'
      · exact h1 h1'
      · exact hA a r hr ⟨R01, R12⟩

lemma idx_app_mem {P : List ℤ} {t x : ℤ} (hx : x ∈ P) : (P ++ [t]).idxOf x = P.idxOf x := by
  rw [List.idxOf_append, if_pos hx]

lemma idx_app_t {P : List ℤ} {t : ℤ} (ht : t ∉ P) : (P ++ [t]).idxOf t = P.length := by
  rw [List.idxOf_append, if_neg ht]; simp

/-- **Far-record append criterion.** If `t` exceeds every continuation `2b−a`, `3b−2a` of pairs
from `P` (e.g. `t > 3·max P − 2·min P`), then appending `t` to a word keeps it safe iff the word
was safe and no element of `P` is `R`-below `t`. -/
theorem safe_append_far {R : ℤ → ℤ → Prop} (hA : No3AP R) (hB : Star R) (P : List ℤ) (t : ℤ)
    (hbig : ∀ a ∈ P, ∀ b ∈ P, 2 * b - a < t ∧ 3 * b - 2 * a < t) :
    Safe R (P ++ [t]) ↔ Safe R P ∧ ∀ a ∈ P, ¬ R a t := by
  have hlt : ∀ b ∈ P, b < t := fun b hb => by have := (hbig b hb b hb).1; linarith
  have htP : t ∉ P := fun h => lt_irrefl _ (hlt t h)
  have hidx : ∀ x ∈ P, P.idxOf x < P.length := fun x hx => List.idxOf_lt_length_of_mem hx
  have hmem : ∀ x, x ∈ P ++ [t] ↔ x ∈ P ∨ x = t := by intro x; simp
  rw [safe_iff_conds hA hB, safe_iff_conds hA hB]
  constructor
  · rintro ⟨hi, hii⟩
    refine ⟨⟨fun a r hr h0 h1 h2 i01 i12 => ?_, fun a r hr h0 h1 i01 hR => ?_⟩, fun a ha hR => ?_⟩
    · have e : (P ++ [t]).idxOf a < (P ++ [t]).idxOf (a + r) := by
        rw [idx_app_mem h0, idx_app_mem h1]; exact i01
      have e' : (P ++ [t]).idxOf (a + r) < (P ++ [t]).idxOf (a + 2 * r) := by
        rw [idx_app_mem h1, idx_app_mem h2]; exact i12
      obtain ⟨h3, n23⟩ := hi a r hr ((hmem _).2 (Or.inl h0)) ((hmem _).2 (Or.inl h1))
        ((hmem _).2 (Or.inl h2)) e e'
      rcases (hmem _).1 h3 with h3 | h3
      · refine ⟨h3, fun i23 => n23 ?_⟩
        rw [idx_app_mem h2, idx_app_mem h3]; exact i23
      · exfalso; apply n23
        rw [idx_app_mem h2, h3, idx_app_t htP]; exact hidx _ h2
    · have e : (P ++ [t]).idxOf a < (P ++ [t]).idxOf (a + r) := by
        rw [idx_app_mem h0, idx_app_mem h1]; exact i01
      rcases hii a r hr ((hmem _).2 (Or.inl h0)) ((hmem _).2 (Or.inl h1)) e hR with h | h
      · rcases (hmem _).1 h with h | h
        · exact Or.inl h
        · exfalso; have h' := (hbig a h0 (a + r) h1).1
          have e : 2 * (a + r) - a = a + 2 * r := by ring
          rw [e, h] at h'; exact lt_irrefl _ h'
      · rcases (hmem _).1 h with h | h
        · exact Or.inr h
        · exfalso; have h' := (hbig a h0 (a + r) h1).2
          have e : 3 * (a + r) - 2 * a = a + 3 * r := by ring
          rw [e, h] at h'; exact lt_irrefl _ h'
    · have hat := hlt a ha
      have hr : t - a ≠ 0 := by intro h; linarith
      have e1 : a + (t - a) = t := by ring
      have e : (P ++ [t]).idxOf a < (P ++ [t]).idxOf (a + (t - a)) := by
        rw [e1, idx_app_mem ha, idx_app_t htP]; exact hidx a ha
      have := hii a (t - a) hr ((hmem _).2 (Or.inl ha)) (by rw [e1]; simp) e (by rw [e1]; exact hR)
      rcases this with h | h
      · rcases (hmem _).1 h with h | h
        · have := hlt _ h; linarith
        · linarith
      · rcases (hmem _).1 h with h | h
        · have := hlt _ h; linarith
        · linarith
  · rintro ⟨⟨hi, hii⟩, hno⟩
    -- every element of the extended word that precedes another one in index lies in `P`
    have hpre : ∀ x y, x ∈ P ++ [t] → y ∈ P ++ [t] →
        (P ++ [t]).idxOf x < (P ++ [t]).idxOf y → x ∈ P := by
      intro x y hx hy hxy
      rcases (hmem _).1 hx with hx | hx
      · exact hx
      · exfalso
        rw [hx, idx_app_t htP] at hxy
        rcases (hmem _).1 hy with hy | hy
        · rw [idx_app_mem hy] at hxy; have := hidx y hy; omega
        · rw [hy, idx_app_t htP] at hxy; omega
    refine ⟨fun a r hr h0 h1 h2 i01 i12 => ?_, fun a r hr h0 h1 i01 hR => ?_⟩
    · have p0 := hpre _ _ h0 h1 i01
      have p1 := hpre _ _ h1 h2 i12
      have p2 : a + 2 * r ∈ P := by
        rcases (hmem _).1 h2 with h | h
        · exact h
        · exfalso; have := (hbig a p0 (a + r) p1).1; rw [← h] at this; linarith
      rw [idx_app_mem p0, idx_app_mem p1] at i01
      rw [idx_app_mem p1, idx_app_mem p2] at i12
      obtain ⟨h3, n23⟩ := hi a r hr p0 p1 p2 i01 i12
      refine ⟨(hmem _).2 (Or.inl h3), ?_⟩
      rw [idx_app_mem p2, idx_app_mem h3]; exact n23
    · have p0 := hpre _ _ h0 h1 i01
      rcases (hmem _).1 h1 with p1 | p1
      · rw [idx_app_mem p0, idx_app_mem p1] at i01
        rcases hii a r hr p0 p1 i01 hR with h | h
        · exact Or.inl ((hmem _).2 (Or.inl h))
        · exact Or.inr ((hmem _).2 (Or.inl h))
      · exfalso; rw [p1] at hR; exact hno a p0 hR

/-- ε-order form (stage-dependent ε allowed): a far record `t` can be appended to a word,
for a given ε, iff the word is ε-safe and `t` is ε-below every letter of the word. -/
theorem epsLt_safe_append_far (ε : ℕ → Bool) (P : List ℤ) (t : ℤ)
    (hbig : ∀ a ∈ P, ∀ b ∈ P, 2 * b - a < t ∧ 3 * b - 2 * a < t) :
    Safe (epsLt ε) (P ++ [t]) ↔ Safe (epsLt ε) P ∧ ∀ a ∈ P, epsLt ε t a := by
  rw [safe_append_far (epsLt_no3AP ε) (epsLt_star' ε) P t hbig]
  have hlt : ∀ b ∈ P, b < t := fun b hb => by have := (hbig b hb b hb).1; linarith
  refine and_congr_right fun _ => forall₂_congr fun a ha => ?_
  have hne : a ≠ t := ne_of_lt (hlt a ha)
  constructor
  · intro h; rcases epsLt_total ε hne with h' | h'
    · exact absurd h' h
    · exact h'
  · exact epsLt_asymm ε

end E195Aux



open Erdos195 in
theorem solution (ε : ℕ → Bool) (P : List ℤ) (t : ℤ)
    (hbig : ∀ a ∈ P, ∀ b ∈ P, 2 * b - a < t ∧ 3 * b - 2 * a < t) :
    Safe (epsLt ε) (P ++ [t]) ↔ Safe (epsLt ε) P ∧ ∀ a ∈ P, epsLt ε t a :=
  E195Aux.epsLt_safe_append_far ε P t hbig
