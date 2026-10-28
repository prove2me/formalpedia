-- Prove2me | solution 1 for Erdos195.epsLt_residue_insert
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T02:52:32.790266+00:00
-- url     : https://prove2.me/submissions/7937c5ed-e211-417d-ae37-2856e1b081eb

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



/-! ## Session 47: one-term extension criterion and below-appends -/

/-- **One-term extension criterion** (abstract `R`). For a safe word `P` and a new letter `t ∉ P`,
`P ++ [t]` is safe iff
(A) every in-order pair `a` before `b` of `P` with `t = 2b − a` has its continuation `3b − 2a` in `P`, and
(B) every `a ∈ P` with `R a t` has `2t − a ∈ P` or `3t − 2a ∈ P`. -/
theorem safe_append_iff {R : ℤ → ℤ → Prop} (hA : No3AP R) (hB : Star R) (P : List ℤ) (t : ℤ)
    (hS : Safe R P) (htP : t ∉ P) :
    Safe R (P ++ [t]) ↔
      (∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ P) ∧
      (∀ a ∈ P, R a t → 2 * t - a ∈ P ∨ 3 * t - 2 * a ∈ P) := by
  have hidx : ∀ x ∈ P, P.idxOf x < P.length := fun x hx => List.idxOf_lt_length_of_mem hx
  have hmem : ∀ x, x ∈ P ++ [t] ↔ x ∈ P ∨ x = t := by intro x; simp
  rw [safe_iff_conds hA hB] at hS
  obtain ⟨hi0, hii0⟩ := hS
  rw [safe_iff_conds hA hB]
  constructor
  · rintro ⟨hi, hii⟩
    refine ⟨fun a ha b hb hab hteq => ?_, fun a ha hR => ?_⟩
    · have hr : b - a ≠ 0 := by
        intro h; have : b = a := by linarith
        rw [this] at hab; exact lt_irrefl _ hab
      have e1 : a + (b - a) = b := by ring
      have e2 : a + 2 * (b - a) = t := by rw [hteq]; ring
      have e3 : a + 3 * (b - a) = 3 * b - 2 * a := by ring
      have i01 : (P ++ [t]).idxOf a < (P ++ [t]).idxOf (a + (b - a)) := by
        rw [e1, idx_app_mem ha, idx_app_mem hb]; exact hab
      have i12 : (P ++ [t]).idxOf (a + (b - a)) < (P ++ [t]).idxOf (a + 2 * (b - a)) := by
        rw [e1, e2, idx_app_mem hb, idx_app_t htP]; exact hidx b hb
      obtain ⟨h3, -⟩ := hi a (b - a) hr ((hmem _).2 (Or.inl ha)) (by rw [e1]; simp [hb])
        (by rw [e2]; simp) i01 i12
      rw [e3] at h3
      rcases (hmem _).1 h3 with h | h
      · exact h
      · exfalso; apply hr; linarith
    · have hat : a ≠ t := fun h => htP (h ▸ ha)
      have hr : t - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hat)
      have e1 : a + (t - a) = t := by ring
      have i01 : (P ++ [t]).idxOf a < (P ++ [t]).idxOf (a + (t - a)) := by
        rw [e1, idx_app_mem ha, idx_app_t htP]; exact hidx a ha
      rcases hii a (t - a) hr ((hmem _).2 (Or.inl ha)) (by rw [e1]; simp) i01 (by rw [e1]; exact hR)
        with h | h
      · have e : a + 2 * (t - a) = 2 * t - a := by ring
        rw [e] at h
        rcases (hmem _).1 h with h | h
        · exact Or.inl h
        · exfalso; apply hr; linarith
      · have e : a + 3 * (t - a) = 3 * t - 2 * a := by ring
        rw [e] at h
        rcases (hmem _).1 h with h | h
        · exact Or.inr h
        · exfalso; apply hr; linarith
  · rintro ⟨hAc, hBc⟩
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
      rw [idx_app_mem p0, idx_app_mem p1] at i01
      rcases (hmem _).1 h2 with p2 | p2
      · rw [idx_app_mem p1, idx_app_mem p2] at i12
        obtain ⟨h3, n23⟩ := hi0 a r hr p0 p1 p2 i01 i12
        refine ⟨(hmem _).2 (Or.inl h3), ?_⟩
        rw [idx_app_mem p2, idx_app_mem h3]; exact n23
      · have h3 := hAc a p0 (a + r) p1 i01 (by rw [← p2]; ring)
        have e3 : 3 * (a + r) - 2 * a = a + 3 * r := by ring
        rw [e3] at h3
        refine ⟨(hmem _).2 (Or.inl h3), ?_⟩
        rw [p2, idx_app_t htP, idx_app_mem h3]
        have := hidx _ h3; omega
    · have p0 := hpre _ _ h0 h1 i01
      rcases (hmem _).1 h1 with p1 | p1
      · rw [idx_app_mem p0, idx_app_mem p1] at i01
        rcases hii0 a r hr p0 p1 i01 hR with h | h
        · exact Or.inl ((hmem _).2 (Or.inl h))
        · exact Or.inr ((hmem _).2 (Or.inl h))
      · rw [p1] at hR
        rcases hBc a p0 hR with h | h
        · left; apply (hmem _).2; left
          have e : 2 * t - a = a + 2 * r := by rw [← p1]; ring
          rw [← e]; exact h
        · right; apply (hmem _).2; left
          have e : 3 * t - 2 * a = a + 3 * r := by rw [← p1]; ring
          rw [← e]; exact h

/-- ε-order form of the one-term extension criterion. -/
theorem epsLt_safe_append_iff (ε : ℕ → Bool) (P : List ℤ) (t : ℤ)
    (hS : Safe (epsLt ε) P) (htP : t ∉ P) :
    Safe (epsLt ε) (P ++ [t]) ↔
      (∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ P) ∧
      (∀ a ∈ P, epsLt ε a t → 2 * t - a ∈ P ∨ 3 * t - 2 * a ∈ P) :=
  safe_append_iff (epsLt_no3AP ε) (epsLt_star' ε) P t hS htP

/-- **Appending a letter below everything.** If `P` is ε-safe and `t` is not in `P`, is not a
3AP-continuation `2b − a` of an in-order pair of `P`, and is ε-below every letter of `P`,
then `P ++ [t]` is ε-safe. (No "far" hypothesis.) -/
theorem epsLt_safe_append_below (ε : ℕ → Bool) (P : List ℤ) (t : ℤ)
    (hS : Safe (epsLt ε) P) (htP : t ∉ P)
    (hF : ∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → t ≠ 2 * b - a)
    (hbelow : ∀ a ∈ P, epsLt ε t a) :
    Safe (epsLt ε) (P ++ [t]) := by
  rw [epsLt_safe_append_iff ε P t hS htP]
  exact ⟨fun a ha b hb hab h => absurd h (hF a ha b hb hab),
    fun a ha h => absurd h (epsLt_asymm ε (hbelow a ha))⟩



/-! ## Existence of below-letters arbitrarily far in both directions -/

/-- If `ε` is not eventually constant, every finite word has a strict ε-lower bound. -/
lemma exists_epsLt_below_all (ε : ℕ → Bool) (hε : ¬ ∃ N : ℕ, ∃ b : Bool, ∀ n ≥ N, ε n = b) :
    ∀ P : List ℤ, ∃ c, ∀ a ∈ P, epsLt ε c a := by
  intro P
  induction P with
  | nil => exact ⟨0, by simp⟩
  | cons x P ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨y, hy⟩ := (epsLt_no_endpoints' ε hε x).1
    by_cases hcx : epsLt ε c x
    · exact ⟨c, by
        intro a ha
        rcases List.mem_cons.1 ha with h | h
        · rw [h]; exact hcx
        · exact hc a h⟩
    · refine ⟨y, ?_⟩
      have hxc : x = c ∨ epsLt ε x c := by
        by_cases h : x = c
        · exact Or.inl h
        · rcases epsLt_total ε h with h' | h'
          · exact Or.inr h'
          · exact absurd h' hcx
      intro a ha
      rcases List.mem_cons.1 ha with h | h
      · rw [h]; exact hy
      · rcases hxc with e | e
        · rw [e] at hy; exact epsLt_trans ε hy (hc a h)
        · exact epsLt_trans ε (epsLt_trans ε hy e) (hc a h)

/-- Shifting by a multiple of a large power of two preserves ε-comparisons with nearby letters. -/
lemma epsLt_shift (ε : ℕ → Bool) {c a : ℤ} {K : ℕ} (hK : |a - c| < 2 ^ K)
    (hc : epsLt ε c a) (s : ℤ) : epsLt ε (c + 2 ^ K * s) a := by
  obtain ⟨hca, hd⟩ := hc
  set d := a - c with hdef
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hca)
  set k := padicValInt 2 d with hkdef
  have hkK : k < K := by
    by_contra h
    push Not at h
    have hdv : (2 : ℤ) ^ K ∣ d := dvd_of_le_val (le_trans h le_rfl)
    obtain ⟨m, hm⟩ := hdv
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hd0 hm
    have : (2 : ℤ) ^ K ≤ |d| := by
      rw [hm, abs_mul, abs_of_pos (by positivity : (0:ℤ) < 2 ^ K)]
      have : 1 ≤ |m| := Int.one_le_abs hm0
      nlinarith [(by positivity : (0:ℤ) < 2 ^ K)]
    linarith
  have hKdvd : (2 : ℤ) ^ (k + 1) ∣ 2 ^ K * s :=
    (pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _)
  have he : a - (c + 2 ^ K * s) = d - 2 ^ K * s := by rw [hdef]; ring
  have hne : d - 2 ^ K * s ≠ 0 := by
    intro h
    have : (2 : ℤ) ^ (k + 1) ∣ d := by
      have : d = 2 ^ K * s := by linarith
      rw [this]; exact hKdvd
    have := le_val_of_dvd hd0 this
    omega
  have hv : padicValInt 2 (d - 2 ^ K * s) = k := by
    apply le_antisymm
    · by_contra h
      push Not at h
      have h1 : (2 : ℤ) ^ (k + 1) ∣ d - 2 ^ K * s := dvd_of_le_val (by omega)
      have h2 : (2 : ℤ) ^ (k + 1) ∣ d := by
        have := dvd_add h1 hKdvd
        simpa using this
      have := le_val_of_dvd hd0 h2
      omega
    · apply le_val_of_dvd hne
      exact dvd_sub (two_pow_val_dvd d) ((pow_dvd_pow 2 (le_of_lt hkK)).trans (dvd_mul_right _ _))
  refine ⟨?_, ?_⟩
  · intro h; apply hne; rw [← he, h]; ring
  · rw [he, hv]
    unfold bitOne at hd ⊢
    have hdig : c / 2 ^ k % 2 = (c + 2 ^ K * s) / 2 ^ k % 2 :=
      digit_eq_of_dvd (by rw [show c + 2 ^ K * s - c = 2 ^ K * s by ring]; exact hKdvd)
    rw [← hdig]
    exact hd

lemma exists_abs_bound (P : List ℤ) : ∃ B : ℤ, 0 ≤ B ∧ ∀ a ∈ P, |a| ≤ B := by
  induction P with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons x P ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    refine ⟨max B |x|, le_trans hB0 (le_max_left _ _), ?_⟩
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · rw [h]; exact le_max_right _ _
    · exact le_trans (hB a h) (le_max_left _ _)

/-- **Unconditional below-appends, arbitrarily far in both directions.** If `ε` is not
eventually constant and `P` is ε-safe, then for every bound `M` there are letters `t > M` and
`t < M`, each ε-below every letter of `P`, such that `P ++ [t]` is ε-safe. -/
theorem epsLt_exists_safe_append_below (ε : ℕ → Bool)
    (hε : ¬ ∃ N : ℕ, ∃ b : Bool, ∀ n ≥ N, ε n = b) (P : List ℤ) (hS : Safe (epsLt ε) P) (M : ℤ) :
    (∃ t, M < t ∧ (∀ a ∈ P, epsLt ε t a) ∧ Safe (epsLt ε) (P ++ [t])) ∧
    (∃ t, t < M ∧ (∀ a ∈ P, epsLt ε t a) ∧ Safe (epsLt ε) (P ++ [t])) := by
  obtain ⟨c, hc⟩ := exists_epsLt_below_all ε hε P
  obtain ⟨B, hB0, hB⟩ := exists_abs_bound P
  set n := (B + |c|).toNat with hn
  have hn' : B + |c| ≤ (n : ℤ) := by rw [hn]; exact Int.self_le_toNat _
  have h2n : (n : ℤ) < 2 ^ n := by exact_mod_cast n.lt_two_pow_self
  have hK : ∀ a ∈ P, |a - c| < 2 ^ n := by
    intro a ha
    have := abs_sub a c
    have := hB a ha
    linarith
  have hbelow : ∀ s : ℤ, ∀ a ∈ P, epsLt ε (c + 2 ^ n * s) a :=
    fun s a ha => epsLt_shift ε (hK a ha) (hc a ha) s
  have hpow : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have habs : ∀ a ∈ P, -B ≤ a ∧ a ≤ B := fun a ha => abs_le.1 (hB a ha)
  have hc' := abs_le.1 (le_refl |c|)
  -- general appending step for a letter outside `[-3B, 3B]`
  have step : ∀ t, (3 * B < t ∨ t < -3 * B) → (∀ a ∈ P, epsLt ε t a) →
      Safe (epsLt ε) (P ++ [t]) := by
    intro t ht hbt
    apply epsLt_safe_append_below ε P t hS
    · intro h; have := habs t h; rcases ht with ht | ht <;> linarith
    · intro a ha b hb _ h
      have := habs a ha; have := habs b hb
      rcases ht with ht | ht <;> linarith
    · exact hbt
  set s := |M| + 3 * B + |c| + 1 with hs
  have hM := abs_le.1 (le_refl |M|)
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  refine ⟨⟨c + 2 ^ n * s, ?_, hbelow s, step _ (Or.inl ?_) (hbelow s)⟩,
    ⟨c + 2 ^ n * (-s), ?_, hbelow (-s), step _ (Or.inr ?_) (hbelow (-s))⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith




/-! ## Session 48: block appends below the word, residue-class insertion -/

/-- Main step of the block lemma: the whole block `S` can be appended. -/
theorem epsLt_safe_append_block_all (ε : ℕ → Bool) (P : List ℤ) (hS : Safe (epsLt ε) P) :
    ∀ S : List ℤ, (∀ s ∈ S, s ∉ P) → (∀ s ∈ S, ∀ p ∈ P, epsLt ε s p) →
      S.Pairwise (fun x y => epsLt ε y x) →
      (∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → 2 * b - a ∈ S → 3 * b - 2 * a ∈ P) →
      Safe (epsLt ε) (P ++ S) := by
  intro S
  induction S using List.reverseRecOn with
  | nil => intros; simpa using hS
  | append_singleton S t ih =>
    intro hdisj hbelow hdec hF
    have hdecS : S.Pairwise (fun x y => epsLt ε y x) := (List.pairwise_append.1 hdec).1
    have htS : ∀ x ∈ S, epsLt ε t x := fun x hx =>
      (List.pairwise_append.1 hdec).2.2 x hx t (by simp)
    have hIH : Safe (epsLt ε) (P ++ S) :=
      ih (fun s hs => hdisj s (by simp [hs])) (fun s hs => hbelow s (by simp [hs])) hdecS
        (fun a ha b hb hab h => hF a ha b hb hab (by simp [h]))
    have htP : t ∉ P := hdisj t (by simp)
    have htPS : t ∉ P ++ S := by
      intro h
      rcases List.mem_append.1 h with h | h
      · exact htP h
      · exact (htS t h).1 rfl
    -- `t` is below every letter of `P ++ S`
    have htall : ∀ x ∈ P ++ S, epsLt ε t x := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hbelow t (by simp) x h
      · exact htS x h
    rw [← List.append_assoc, epsLt_safe_append_iff ε (P ++ S) t hIH htPS]
    refine ⟨fun a ha b hb hab hteq => ?_, fun a ha h => absurd h (epsLt_asymm ε (htall a ha))⟩
    by_cases hbP : b ∈ P
    · -- then `a ∈ P` as well
      have haP : a ∈ P := by
        by_contra haP
        rw [List.idxOf_append, List.idxOf_append, if_neg haP, if_pos hbP] at hab
        have := List.idxOf_lt_length_of_mem hbP
        omega
      rw [List.idxOf_append, List.idxOf_append, if_pos haP, if_pos hbP] at hab
      exact List.mem_append_left _ (hF a haP b hbP hab (by rw [← hteq]; simp))
    · -- `b` lies in the block: `t ≺ b ≺ a` is a monotone 3AP
      exfalso
      have hbS : b ∈ S := by
        rcases List.mem_append.1 hb with h | h
        · exact absurd h hbP
        · exact h
      have hba : epsLt ε b a := by
        by_cases haP : a ∈ P
        · exact hbelow b (by simp [hbS]) a haP
        · have haS : a ∈ S := by
            rcases List.mem_append.1 ha with h | h
            · exact absurd h haP
            · exact h
          rw [List.idxOf_append, List.idxOf_append, if_neg haP, if_neg hbP] at hab
          exact pairwise_idx hdecS haS hbS (by omega)
      have htb : epsLt ε t b := htS b hbS
      have hr : b - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htb.1)
      apply epsLt_no_3AP ε (a := t) hr
      have e1 : t + (b - t) = b := by ring
      have e2 : t + 2 * (b - t) = a := by rw [hteq]; ring
      rw [e1, e2]
      exact ⟨htb, hba⟩

/-- **Block lemma** (Astra's Lemma 1). If `P` is ε-safe, `S` is a list of letters not in `P`,
each ε-below every letter of `P`, listed in ε-decreasing order, and every in-order pair `a, b`
of `P` whose 3AP-continuation `2b − a` lies in `S` has `3b − 2a ∈ P`, then every word
`P ++ (first j letters of S)` is ε-safe. -/
theorem epsLt_safe_append_block (ε : ℕ → Bool) (P S : List ℤ) (hS : Safe (epsLt ε) P)
    (hdisj : ∀ s ∈ S, s ∉ P) (hbelow : ∀ s ∈ S, ∀ p ∈ P, epsLt ε s p)
    (hdec : S.Pairwise (fun x y => epsLt ε y x))
    (hF : ∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → 2 * b - a ∈ S → 3 * b - 2 * a ∈ P) :
    ∀ j : ℕ, Safe (epsLt ε) (P ++ S.take j) := by
  intro j
  have hsub : ∀ x ∈ S.take j, x ∈ S := fun x hx => List.mem_of_mem_take hx
  exact epsLt_safe_append_block_all ε P hS (S.take j) (fun s hs => hdisj s (hsub s hs))
    (fun s hs => hbelow s (hsub s hs)) (hdec.sublist (List.take_sublist j S))
    (fun a ha b hb hab h => hF a ha b hb hab (hsub _ h))

/-- The ε-order induced by a residue class: digits below `m` are "opposite to `r`". -/
def resEps (ε : ℕ → Bool) (m : ℕ) (r : ℤ) : ℕ → Bool :=
  fun k => if k < m then decide (r / 2 ^ k % 2 = 0) else ε k

/-- Changing ε only below `m` does not change comparisons of letters congruent mod `2^m`. -/
lemma epsLt_congr_of_dvd (ε ε' : ℕ → Bool) (m : ℕ) (hε : ∀ k, m ≤ k → ε' k = ε k)
    {a b : ℤ} (hab : (2 : ℤ) ^ m ∣ b - a) : epsLt ε' a b ↔ epsLt ε a b := by
  by_cases h : a = b
  · subst h; simp [epsLt]
  · have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hk := le_val_of_dvd hne hab
    unfold epsLt
    rw [hε _ hk]

/-- Safety of `P` only depends on `R` restricted to pairs of letters of `P`. -/
lemma safeConds_congr {R R' : ℤ → ℤ → Prop} (P : List ℤ)
    (h : ∀ x ∈ P, ∀ y ∈ P, (R' x y ↔ R x y)) : SafeConds R' P ↔ SafeConds R P := by
  unfold SafeConds
  refine and_congr_right fun _ => ?_
  constructor
  · intro H a r hr h0 h1 i hR; exact H a r hr h0 h1 i ((h _ h0 _ h1).2 hR)
  · intro H a r hr h0 h1 i hR; exact H a r hr h0 h1 i ((h _ h0 _ h1).1 hR)

/-- A letter outside the residue class `r + 2^m ℤ` is `resEps`-below every letter inside it. -/
lemma resEps_below (ε : ℕ → Bool) (m : ℕ) (r : ℤ) {s p : ℤ}
    (hs : ¬ (2 : ℤ) ^ m ∣ s - r) (hp : (2 : ℤ) ^ m ∣ p - r) : epsLt (resEps ε m r) s p := by
  have hsp : s ≠ p := by rintro rfl; exact hs hp
  have hne : p - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsp)
  set k := padicValInt 2 (p - s) with hk
  have hkm : k < m := by
    by_contra hc
    push Not at hc
    apply hs
    have : (2 : ℤ) ^ m ∣ p - s := dvd_of_le_val hc
    have e : s - r = (p - r) - (p - s) := by ring
    rw [e]; exact dvd_sub hp this
  have hpr : p / 2 ^ k % 2 = r / 2 ^ k % 2 :=
    (digit_eq_of_dvd (x := r) (y := p) ((pow_dvd_pow 2 (by omega)).trans hp)).symm
  have dn := digit_ne hsp
  rw [← hk] at dn
  refine ⟨hsp, ?_⟩
  unfold bitOne resEps
  rw [← hk, if_pos hkm]
  rw [hpr] at dn
  have h01 : r / 2 ^ k % 2 = 0 ∨ r / 2 ^ k % 2 = 1 := by omega
  rcases h01 with h0 | h1
  · simp only [h0, decide_true, iff_true]
    rw [h0] at dn; omega
  · simp only [h1, decide_eq_true_eq]
    rw [h1] at dn; omega

/-- An ε-decreasing arrangement of any duplicate-free list. -/
lemma exists_epsLt_dec_perm (ε : ℕ → Bool) (S : List ℤ) (hS : S.Nodup) :
    ∃ S' : List ℤ, S'.Perm S ∧ S'.Pairwise (fun x y => epsLt ε y x) := by
  classical
  let rel : ℤ → ℤ → Prop := fun x y => x = y ∨ epsLt ε y x
  haveI : IsTotal ℤ rel := ⟨fun x y => by
    by_cases h : x = y
    · exact Or.inl (Or.inl h)
    · rcases epsLt_total ε h with h' | h'
      · exact Or.inr (Or.inr h')
      · exact Or.inl (Or.inr h')⟩
  haveI : IsTrans ℤ rel := ⟨fun x y z h1 h2 => by
    rcases h1 with rfl | h1
    · exact h2
    · rcases h2 with rfl | h2
      · exact Or.inr h1
      · exact Or.inr (epsLt_trans ε h2 h1)⟩
  refine ⟨S.insertionSort rel, List.perm_insertionSort rel S, ?_⟩
  have hsorted := List.pairwise_insertionSort rel S
  have hnd : (S.insertionSort rel).Nodup := (List.perm_insertionSort rel S).nodup_iff.2 hS
  exact (hsorted.and hnd).imp fun ⟨h1, h2⟩ => h1.resolve_left h2

/-- **Residue-class insertion** (Astra's Theorem 2). Let `P` be ε-safe with all letters
`≡ r (mod 2^m)`. Put `ε'_k = 1 − bit_k(r)` for `k < m` and `ε'_k = ε_k` for `k ≥ m`. Then every
finite duplicate-free set `S` of integers `≢ r (mod 2^m)` can be arranged as a list `S'` such that
`P ++ (first j letters of S')` is ε'-safe for every `j` (in particular `P ++ S'` is). Moreover
every letter of `S` is ε'-below every letter of `P`. -/
theorem epsLt_residue_insert (ε : ℕ → Bool) (m : ℕ) (r : ℤ) (P : List ℤ)
    (hS : Safe (epsLt ε) P) (hP : ∀ p ∈ P, (2 : ℤ) ^ m ∣ p - r)
    (S : List ℤ) (hSnd : S.Nodup) (hSr : ∀ s ∈ S, ¬ (2 : ℤ) ^ m ∣ s - r) :
    ∃ S' : List ℤ, S'.Perm S ∧
      (∀ s ∈ S, ∀ p ∈ P, epsLt (resEps ε m r) s p) ∧
      ∀ j : ℕ, Safe (epsLt (resEps ε m r)) (P ++ S'.take j) := by
  set ε' := resEps ε m r with hε'
  have hhigh : ∀ k, m ≤ k → ε' k = ε k := fun k hk => by
    simp [hε', resEps, show ¬ k < m by omega]
  -- `P` stays safe for `ε'`
  have hS' : Safe (epsLt ε') P := by
    rw [safe_iff_conds (epsLt_no3AP ε') (epsLt_star' ε')]
    rw [safe_iff_conds (epsLt_no3AP ε) (epsLt_star' ε)] at hS
    refine (safeConds_congr P fun x hx y hy => ?_).2 hS
    apply epsLt_congr_of_dvd ε ε' m hhigh
    have e : y - x = (y - r) - (x - r) := by ring
    rw [e]; exact dvd_sub (hP y hy) (hP x hx)
  obtain ⟨S', hperm, hdec⟩ := exists_epsLt_dec_perm ε' S hSnd
  have hmem : ∀ s ∈ S', s ∈ S := fun s hs => hperm.subset hs
  have hbelowS : ∀ s ∈ S, ∀ p ∈ P, epsLt ε' s p := fun s hs p hp =>
    resEps_below ε m r (hSr s hs) (hP p hp)
  refine ⟨S', hperm, hbelowS, ?_⟩
  apply epsLt_safe_append_block ε' P S' hS'
  · intro s hs hsP; exact hSr s (hmem s hs) (hP s hsP)
  · exact fun s hs => hbelowS s (hmem s hs)
  · exact hdec
  · intro a ha b hb _ h
    exfalso
    apply hSr _ (hmem _ h)
    have e : 2 * b - a - r = 2 * (b - r) - (a - r) := by ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_right (hP b hb) 2) (hP a ha)

end E195Aux



open Erdos195 in
theorem solution (ε : ℕ → Bool) (m : ℕ) (r : ℤ) (P : List ℤ)
    (hS : Safe (epsLt ε) P) (hP : ∀ p ∈ P, (2 : ℤ) ^ m ∣ p - r)
    (S : List ℤ) (hSnd : S.Nodup) (hSr : ∀ s ∈ S, ¬ (2 : ℤ) ^ m ∣ s - r) :
    ∃ S' : List ℤ, S'.Perm S ∧
      (∀ s ∈ S, ∀ p ∈ P,
        epsLt (fun k => if k < m then decide (r / 2 ^ k % 2 = 0) else ε k) s p) ∧
      ∀ j : ℕ, Safe (epsLt (fun k => if k < m then decide (r / 2 ^ k % 2 = 0) else ε k))
        (P ++ S'.take j) :=
  E195Aux.epsLt_residue_insert ε m r P hS hP S hSnd hSr
