-- Prove2me | solution 1 for Erdos195.epsLt_no3AP
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T21:24:12.228755+00:00
-- url     : https://prove2.me/submissions/eac9c2e6-0f26-4ca0-8bad-8d49aeee3d4c

import Mathlib
import Definitions.Def_Erdos195_defs



namespace Erdos195.Aux


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


end Erdos195.Aux

namespace Erdos195

theorem epsLt_isStrictTotalOrder (ε : ℕ → Bool) : IsStrictTotalOrder ℤ (epsLt ε) :=
  Aux.epsLt_isStrictTotalOrder' ε

theorem epsLt_no3AP (ε : ℕ → Bool) : No3AP (epsLt ε) := Aux.epsLt_no3AP ε

theorem epsLt_star (ε : ℕ → Bool) : Star (epsLt ε) := Aux.epsLt_star' ε

theorem epsLt_no_endpoints (ε : ℕ → Bool) (hε : ¬ ∃ N : ℕ, ∃ b : Bool, ∀ n ≥ N, ε n = b)
    (x : ℤ) : (∃ y, epsLt ε y x) ∧ (∃ y, epsLt ε x y) := Aux.epsLt_no_endpoints' ε hε x

theorem twosComplement_neg_one_least (y : ℤ) (hy : y ≠ -1) : epsLt (fun _ => true) (-1) y :=
  Aux.neg_one_least hy

theorem epsLt_safe_of_reverse (ε : ℕ → Bool) (P : List ℤ)
    (hP : P.Pairwise (fun x y => epsLt ε y x)) : Safe (epsLt ε) P := Aux.epsLt_safe_of_rev ε hP

theorem extremum_obstruction (R : ℤ → ℤ → Prop) (hB : Star R) (z : ℤ)
    (hz : ∀ y, y ≠ z → R z y) (P : List ℤ) (hS : Safe R P) (hzP : z ∈ P) (M : ℤ)
    (hMP : M ∈ P) (hzM : P.idxOf z < P.idxOf M)
    (hext : (∀ x ∈ P, x ≤ M) ∨ (∀ x ∈ P, M ≤ x)) : False :=
  Aux.extremum_obstruction hB hz hS hzP hMP hzM hext

theorem twosComplement_no_exhaustive_safe_chain (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (fun _ => true)) (P n))
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x, ∃ n, x ∈ P n) : False :=
  Aux.no_exhaustive_chain_twos_complement P hsafe hpre hcov

end Erdos195



open Erdos195 in
theorem solution (ε : ℕ → Bool) : No3AP (epsLt ε) :=
  Erdos195.epsLt_no3AP ε
