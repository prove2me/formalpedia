-- Prove2me | solution 1 for Erdos195.safe_odd_affine_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T13:11:50.461751+00:00
-- url     : https://prove2.me/submissions/b433cec1-ec3b-4d9b-b77e-0ae9a34e7d5c

import Mathlib
import Definitions.Def_Erdos195_tree


namespace E195Tree
open Erdos195

lemma two_pow_val_dvd (r : ℤ) : (2 : ℤ) ^ padicValInt 2 r ∣ r := by
  have := padicValInt_dvd (p := 2) r
  simpa using this

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

lemma div_pow_add_mul (a r j : ℤ) :
    (a + j * r) / 2 ^ padicValInt 2 r = a / 2 ^ padicValInt 2 r + j * (r / 2 ^ padicValInt 2 r) := by
  have h : (2 : ℤ) ^ padicValInt 2 r ≠ 0 := pow_ne_zero _ (by norm_num)
  have e : a + j * r = a + (j * (r / 2 ^ padicValInt 2 r)) * 2 ^ padicValInt 2 r := by
    rw [mul_assoc, Int.ediv_mul_cancel (two_pow_val_dvd r)]
  rw [e, Int.add_mul_ediv_right _ _ h]

lemma dvd_of_le_val {d : ℤ} {n : ℕ} (h : n ≤ padicValInt 2 d) : (2 : ℤ) ^ n ∣ d :=
  (pow_dvd_pow 2 h).trans (two_pow_val_dvd d)

lemma le_val_of_dvd {d : ℤ} (hd : d ≠ 0) {n : ℕ} (h : (2 : ℤ) ^ n ∣ d) : n ≤ padicValInt 2 d := by
  have h' : ((2 : ℕ) : ℤ) ^ n ∣ d := by exact_mod_cast h
  rcases (padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) n d).1 h' with h0 | h0
  · exact absurd h0 hd
  · exact h0

lemma digit_eq_of_dvd {x y : ℤ} {j : ℕ} (h : (2 : ℤ) ^ (j + 1) ∣ y - x) :
    x / 2 ^ j % 2 = y / 2 ^ j % 2 := by
  obtain ⟨t, ht⟩ := h
  have hy : y = x + (2 * t) * 2 ^ j := by rw [pow_succ] at ht; linarith
  have h0 : (2 : ℤ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hy, Int.add_mul_ediv_right _ _ h0]
  omega

lemma digit_ne {x y : ℤ} (hne : x ≠ y) :
    (y / 2 ^ padicValInt 2 (y - x) % 2 = 1 ↔ ¬ x / 2 ^ padicValInt 2 (y - x) % 2 = 1) := by
  have hr : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hq := odd_part (y - x) hr
  have hy := div_pow_add_mul x (y - x) 1
  rw [show x + 1 * (y - x) = y by ring, one_mul] at hy
  rw [hy]
  omega

lemma padicValInt_sub_comm (x y : ℤ) : padicValInt 2 (x - y) = padicValInt 2 (y - x) := by
  rw [padicValInt, padicValInt, ← Int.natAbs_neg, neg_sub]

lemma emod_eq_of_dvd {x y : ℤ} {k : ℕ} (h : (2 : ℤ) ^ k ∣ y - x) : x % 2 ^ k = y % 2 ^ k :=
  (Int.modEq_iff_dvd.2 h)

/-- bit flip at the difference valuation, as `bitOne`. -/
lemma bit_ne {x y : ℤ} (hne : x ≠ y) :
    (bitOne y (padicValInt 2 (y - x)) ↔ ¬ bitOne x (padicValInt 2 (y - x))) := digit_ne hne

lemma treeLt_step (θ : ℕ → ℤ → Bool) {a r : ℤ} (hr : r ≠ 0) (j : ℤ) :
    treeLt θ (a + j * r) (a + (j + 1) * r) ↔
      ((a / 2 ^ padicValInt 2 r + j * (r / 2 ^ padicValInt 2 r)) % 2 = 1 ↔
        θ (padicValInt 2 r) (a % 2 ^ padicValInt 2 r) = true) := by
  have hdiff : a + (j + 1) * r - (a + j * r) = r := by ring
  have hm : (a + j * r) % 2 ^ padicValInt 2 r = a % 2 ^ padicValInt 2 r :=
    (emod_eq_of_dvd (by rw [show a + j * r - a = j * r by ring]; exact
      (two_pow_val_dvd r).mul_left j)).symm
  unfold treeLt bitOne
  rw [hdiff, div_pow_add_mul, hm]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by intro h'; apply hr; linarith, h⟩

lemma parity_alt {A q : ℤ} (hq : q % 2 = 1) (j : ℤ) :
    ((A + (j + 1) * q) % 2 = 1 ↔ ¬ (A + j * q) % 2 = 1) := by
  have : A + (j + 1) * q = (A + j * q) + q := by ring
  rw [this]; omega

theorem treeLt_no3AP (θ : ℕ → ℤ → Bool) : No3AP (treeLt θ) := by
  intro a r hr ⟨h1, h2⟩
  have e1 := (treeLt_step θ (a := a) hr 0).1 (by simpa using h1)
  have e2 := (treeLt_step θ (a := a) hr 1).1 (by
    have : a + 1 * r = a + r := by ring
    have h' : a + (1 + 1) * r = a + 2 * r := by ring
    rw [this, h']; exact h2)
  have hq1 := odd_part r hr
  have := parity_alt (A := a / 2 ^ padicValInt 2 r) hq1 0
  simp only [zero_add, one_mul, zero_mul, add_zero] at this e1 e2
  tauto

theorem treeLt_star (θ : ℕ → ℤ → Bool) : Star (treeLt θ) := by
  intro a r hr
  have h0 := treeLt_step θ (a := a) hr 0
  have h2 := treeLt_step θ (a := a) hr 2
  simp only [zero_mul, add_zero, zero_add, one_mul] at h0
  have e2 : a + (2 + 1) * r = a + 3 * r := by ring
  rw [e2] at h2
  rw [h0, h2]
  have : (a / 2 ^ padicValInt 2 r + 2 * (r / 2 ^ padicValInt 2 r)) % 2 =
      (a / 2 ^ padicValInt 2 r) % 2 := by omega
  rw [this]

theorem treeLt_trans (θ : ℕ → ℤ → Bool) {x y z : ℤ} (h1 : treeLt θ x y) (h2 : treeLt θ y z) :
    treeLt θ x z := by
  obtain ⟨hxy, c1⟩ := h1
  obtain ⟨hyz, c2⟩ := h2
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
  · have hd2 : (2 : ℤ) ^ (k1 + 1) ∣ z - y := dvd_of_le_val (by omega)
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
    rw [hk3]; exact c1
  · exfalso
    have dn := bit_ne hxy
    rw [← hk1] at dn
    rw [← heq] at c2
    have hm : x % 2 ^ k1 = y % 2 ^ k1 := emod_eq_of_dvd (two_pow_val_dvd _)
    rw [hm] at c1
    tauto
  · have hd1 : (2 : ℤ) ^ (k2 + 1) ∣ y - x := dvd_of_le_val (by omega)
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
    have hm : x % 2 ^ k2 = y % 2 ^ k2 := emod_eq_of_dvd hd1'
    unfold bitOne at c2 ⊢
    rw [hk3, hm, digit_eq_of_dvd hd1]; exact c2

theorem treeLt_total (θ : ℕ → ℤ → Bool) {x y : ℤ} (hne : x ≠ y) :
    treeLt θ x y ∨ treeLt θ y x := by
  by_cases h : (bitOne x (padicValInt 2 (y - x)) ↔
      θ (padicValInt 2 (y - x)) (x % 2 ^ padicValInt 2 (y - x)) = true)
  · exact Or.inl ⟨hne, h⟩
  · right
    refine ⟨Ne.symm hne, ?_⟩
    rw [padicValInt_sub_comm]
    have dn := bit_ne hne
    have hm : x % 2 ^ padicValInt 2 (y - x) = y % 2 ^ padicValInt 2 (y - x) :=
      emod_eq_of_dvd (two_pow_val_dvd _)
    rw [← hm]
    tauto

end E195Tree

namespace Erdos195
open E195Tree

theorem treeLt_isStrictTotalOrder (θ : ℕ → ℤ → Bool) : IsStrictTotalOrder ℤ (treeLt θ) where
  trichotomous a b h1 h2 := by
    by_contra hne
    rcases treeLt_total θ hne with h | h
    · exact h1 h
    · exact h2 h
  irrefl a h := h.1 rfl
  trans a b c h1 h2 := treeLt_trans θ h1 h2

/-- **Tree orders (Astra tree Thm 1).** -/
theorem treeLt_order_props (θ : ℕ → ℤ → Bool) :
    IsStrictTotalOrder ℤ (treeLt θ) ∧ No3AP (treeLt θ) ∧ Star (treeLt θ) :=
  ⟨treeLt_isStrictTotalOrder θ, treeLt_no3AP θ, treeLt_star θ⟩

/-- Ordinary ε-orders are the tree orders with node-independent witness. -/
theorem treeLt_const_eq_epsLt (ε : ℕ → Bool) : treeLt (fun k _ => ε k) = epsLt ε := rfl

end Erdos195

namespace E195Tree
open Erdos195

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
      push Not at hc
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

/-- In-order 3-AP condition. -/
def APC (Q : List ℤ) : Prop :=
  ∀ a b : ℤ, a ∈ Q → b ∈ Q → 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b →
    Q.idxOf b < Q.idxOf (2 * b - a) →
    3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)

lemma idx_ne {Q : List ℤ} {x y : ℤ} (hx : x ∈ Q) (hne : x ≠ y) : Q.idxOf x ≠ Q.idxOf y := by
  intro h
  exact hne ((List.idxOf_inj hx).1 h)

lemma conds_iff (R : ℤ → ℤ → Prop) (Q : List ℤ) :
    SafeConds R Q ↔ APC Q ∧ (∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
      2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → ¬ R a b) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b ha hb hc i1 i2 => ?_, fun a b ha hb i1 n2 n3 hR => ?_⟩
    · have hr : b - a ≠ 0 := by
        intro h; have : b = a := by linarith
        subst this; exact lt_irrefl _ i1
      have e1 : a + (b - a) = b := by ring
      have e2 : a + 2 * (b - a) = 2 * b - a := by ring
      have e3 : a + 3 * (b - a) = 3 * b - 2 * a := by ring
      have := h1 a (b - a) hr ha (by rw [e1]; exact hb) (by rw [e2]; exact hc)
        (by rw [e1]; exact i1) (by rw [e1, e2]; exact i2)
      rw [e2, e3] at this
      refine ⟨this.1, ?_⟩
      have hne : 3 * b - 2 * a ≠ 2 * b - a := by intro h; apply hr; linarith
      have := idx_ne this.1 hne
      omega
    · have hr : b - a ≠ 0 := by
        intro h; have : b = a := by linarith
        subst this; exact lt_irrefl _ i1
      have e1 : a + (b - a) = b := by ring
      have e2 : a + 2 * (b - a) = 2 * b - a := by ring
      have e3 : a + 3 * (b - a) = 3 * b - 2 * a := by ring
      have := h2 a (b - a) hr ha (by rw [e1]; exact hb) (by rw [e1]; exact i1)
        (by rw [e1]; exact hR)
      rw [e2, e3] at this
      tauto
  · rintro ⟨h1, h2⟩
    refine ⟨fun a r hr h0 h1' h2' i01 i12 => ?_, fun a r hr h0 h1' i01 hR => ?_⟩
    · have e2 : 2 * (a + r) - a = a + 2 * r := by ring
      have e3 : 3 * (a + r) - 2 * a = a + 3 * r := by ring
      have := h1 a (a + r) h0 h1' (by rw [e2]; exact h2') i01 (by rw [e2]; exact i12)
      rw [e2, e3] at this
      exact ⟨this.1, by omega⟩
    · have e2 : 2 * (a + r) - a = a + 2 * r := by ring
      have e3 : 3 * (a + r) - 2 * a = a + 3 * r := by ring
      by_contra hc
      push Not at hc
      exact h2 a (a + r) h0 h1' i01 (by rw [e2]; exact hc.1) (by rw [e3]; exact hc.2) hR

lemma not_treeLt_iff (θ : ℕ → ℤ → Bool) {a b : ℤ} (hne : a ≠ b) :
    ¬ treeLt θ a b ↔ (θ (padicValInt 2 (b - a)) (a % 2 ^ padicValInt 2 (b - a)) = true ↔
      bitOne b (padicValInt 2 (b - a))) := by
  have dn := bit_ne hne
  unfold treeLt
  constructor
  · intro h
    have : ¬ (bitOne a (padicValInt 2 (b - a)) ↔
        θ (padicValInt 2 (b - a)) (a % 2 ^ padicValInt 2 (b - a)) = true) :=
      fun h' => h ⟨hne, h'⟩
    tauto
  · rintro h ⟨-, h'⟩
    tauto

lemma ne_of_idx {Q : List ℤ} {a b : ℤ} (h : Q.idxOf a < Q.idxOf b) : a ≠ b := by
  rintro rfl; exact lt_irrefl _ h

end E195Tree

namespace Erdos195
open E195Tree

/-- **Tree characterization (Astra tree Thm 2).** -/
theorem treeLt_safe_iff (θ : ℕ → ℤ → Bool) (Q : List ℤ) :
    Safe (treeLt θ) Q ↔
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b →
          Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
          2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
          (θ (padicValInt 2 (b - a)) (a % 2 ^ padicValInt 2 (b - a)) = true ↔
            bitOne b (padicValInt 2 (b - a)))) := by
  rw [safe_iff_conds (treeLt_no3AP θ) (treeLt_star θ), conds_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b ha hb i n2 n3 => (not_treeLt_iff θ (ne_of_idx i)).1 (h2 a b ha hb i n2 n3)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b ha hb i n2 n3 => (not_treeLt_iff θ (ne_of_idx i)).2 (h2 a b ha hb i n2 n3)⟩

/-- **Safe for some tree witness iff no same-node conflict (Astra tree Thm 2, second part).** -/
theorem exists_treeLt_safe_iff (Q : List ℤ) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ↔
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b →
          Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
      (∀ a b a' b' : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
          2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
          a' ∈ Q → b' ∈ Q → Q.idxOf a' < Q.idxOf b' →
          2 * b' - a' ∉ Q → 3 * b' - 2 * a' ∉ Q →
          padicValInt 2 (b - a) = padicValInt 2 (b' - a') →
          a % 2 ^ padicValInt 2 (b - a) = a' % 2 ^ padicValInt 2 (b - a) →
          (bitOne b (padicValInt 2 (b - a)) ↔ bitOne b' (padicValInt 2 (b - a)))) := by
  constructor
  · rintro ⟨θ, hS⟩
    obtain ⟨h1, h2⟩ := (treeLt_safe_iff θ Q).1 hS
    refine ⟨h1, fun a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk hr => ?_⟩
    have c := h2 a b ha hb i n2 n3
    have c' := h2 a' b' ha' hb' i' n2' n3'
    rw [← hk] at c'
    rw [← hr] at c'
    exact c.symm.trans c'
  · rintro ⟨h1, h2⟩
    classical
    let θ : ℕ → ℤ → Bool := fun k r => decide (∃ a b : ℤ, a ∈ Q ∧ b ∈ Q ∧
      Q.idxOf a < Q.idxOf b ∧ 2 * b - a ∉ Q ∧ 3 * b - 2 * a ∉ Q ∧
      padicValInt 2 (b - a) = k ∧ a % 2 ^ k = r ∧ bitOne b k)
    refine ⟨θ, (treeLt_safe_iff θ Q).2 ⟨h1, fun a b ha hb i n2 n3 => ?_⟩⟩
    simp only [θ, decide_eq_true_eq]
    constructor
    · rintro ⟨a', b', ha', hb', i', n2', n3', hk, hr, hbit⟩
      have := h2 a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk.symm hr.symm
      exact this.2 hbit
    · intro hbit
      exact ⟨a, b, ha, hb, i, n2, n3, rfl, rfl, hbit⟩

end Erdos195

namespace E195Par
open Erdos195 E195Tree

/-- Pair conditions of the tree characterization. -/
def C1 (Q : List ℤ) (a b : ℤ) : Prop :=
  a ∈ Q → b ∈ Q → 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b → Q.idxOf b < Q.idxOf (2 * b - a) →
    3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)

def C2 (θ : ℕ → ℤ → Bool) (Q : List ℤ) (a b : ℤ) : Prop :=
  a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
    (θ (padicValInt 2 (b - a)) (a % 2 ^ padicValInt 2 (b - a)) = true ↔
      bitOne b (padicValInt 2 (b - a)))

lemma safe_iff_C (θ : ℕ → ℤ → Bool) (Q : List ℤ) :
    Safe (treeLt θ) Q ↔ ∀ a b, C1 Q a b ∧ C2 θ Q a b := by
  rw [treeLt_safe_iff]
  constructor
  · rintro ⟨h1, h2⟩ a b
    exact ⟨fun ha hb hc i1 i2 => h1 a b ha hb hc i1 i2, fun ha hb i n2 n3 => h2 a b ha hb i n2 n3⟩
  · intro h
    exact ⟨fun a b ha hb hc i1 i2 => (h a b).1 ha hb hc i1 i2,
      fun a b ha hb i n2 n3 => (h a b).2 ha hb i n2 n3⟩

/-- Filtering preserves the relative order of first occurrences. -/
lemma idx_filter (p : ℤ → Bool) {x y : ℤ} (hx : p x = true) (hy : p y = true) :
    ∀ Q : List ℤ, (Q.filter p).idxOf x < (Q.filter p).idxOf y ↔ Q.idxOf x < Q.idxOf y := by
  intro Q
  induction Q with
  | nil => simp
  | cons z Q ih =>
    rw [List.filter_cons]
    by_cases hz : p z = true
    · rw [if_pos hz]
      simp only [List.idxOf_cons]
      by_cases e1 : z = x
      · subst e1
        by_cases e2 : z = y
        · subst e2; simp
        · have b2 : (z == y) = false := by simpa using e2
          simp [b2]
      · have b1 : (z == x) = false := by simpa using e1
        by_cases e2 : z = y
        · subst e2; simp [b1]
        · have b2 : (z == y) = false := by simpa using e2
          simp only [b1, b2, cond_false]; rw [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right]; exact ih
    · rw [if_neg hz]
      have e1 : z ≠ x := by rintro rfl; exact hz hx
      have e2 : z ≠ y := by rintro rfl; exact hz hy
      have b1 : (z == x) = false := by simpa using e1
      have b2 : (z == y) = false := by simpa using e2
      simp only [List.idxOf_cons, b1, b2, cond_false]
      rw [ih]; omega

lemma idx_map {f : ℤ → ℤ} (hf : Function.Injective f) (x : ℤ) :
    ∀ Q : List ℤ, (Q.map f).idxOf (f x) = Q.idxOf x := by
  intro Q
  induction Q with
  | nil => simp
  | cons z Q ih =>
    simp only [List.map_cons, List.idxOf_cons]
    by_cases e : z = x
    · subst e; simp
    · have : f z ≠ f x := fun h => e (hf h)
      have b1 : (z == x) = false := by simpa using e
      have b2 : (f z == f x) = false := by simpa using this
      simp only [b1, b2, cond_false, ih]

/-- Closed predicates: a 3-AP started inside `p` stays inside `p`. -/
def Closed (p : ℤ → Bool) : Prop :=
  ∀ a b, p a = true → p b = true → p (2 * b - a) = true ∧ p (3 * b - 2 * a) = true

lemma mem_filter_iff {p : ℤ → Bool} {Q : List ℤ} {x : ℤ} (hx : p x = true) :
    x ∈ Q.filter p ↔ x ∈ Q := by
  simp [List.mem_filter, hx]

lemma C1_filter {p : ℤ → Bool} (hp : Closed p) (Q : List ℤ) {a b : ℤ}
    (ha : p a = true) (hb : p b = true) : C1 (Q.filter p) a b ↔ C1 Q a b := by
  obtain ⟨hc, he⟩ := hp a b ha hb
  unfold C1
  rw [mem_filter_iff ha, mem_filter_iff hb, mem_filter_iff hc, mem_filter_iff he,
    idx_filter p ha hb, idx_filter p hb hc, idx_filter p he hc]

lemma C2_filter {p : ℤ → Bool} (hp : Closed p) (θ : ℕ → ℤ → Bool) (Q : List ℤ) {a b : ℤ}
    (ha : p a = true) (hb : p b = true) : C2 θ (Q.filter p) a b ↔ C2 θ Q a b := by
  obtain ⟨hc, he⟩ := hp a b ha hb
  unfold C2
  rw [mem_filter_iff ha, mem_filter_iff hb, mem_filter_iff hc, mem_filter_iff he,
    idx_filter p ha hb]

lemma C_filter_vac {p : ℤ → Bool} (θ : ℕ → ℤ → Bool) (Q : List ℤ) {a b : ℤ}
    (h : ¬ (p a = true ∧ p b = true)) : C1 (Q.filter p) a b ∧ C2 θ (Q.filter p) a b := by
  constructor
  · intro ha hb; exfalso; exact h ⟨(List.mem_filter.1 ha).2, (List.mem_filter.1 hb).2⟩
  · intro ha hb; exfalso; exact h ⟨(List.mem_filter.1 ha).2, (List.mem_filter.1 hb).2⟩

/-- **Restriction lemma.** Restricting a tree-safe word to a 3-AP-closed predicate keeps it safe. -/
theorem safe_filter {p : ℤ → Bool} (hp : Closed p) (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) : Safe (treeLt θ) (Q.filter p) := by
  rw [safe_iff_C] at hS ⊢
  intro a b
  by_cases h : p a = true ∧ p b = true
  · exact ⟨(C1_filter hp Q h.1 h.2).2 (hS a b).1, (C2_filter hp θ Q h.1 h.2).2 (hS a b).2⟩
  · exact C_filter_vac θ Q h

lemma closed_mod (m c : ℤ) : Closed (fun x => decide (x % m = c)) := by
  intro a b ha hb
  simp only [decide_eq_true_eq] at ha hb ⊢
  have h : Int.ModEq m b a := hb.trans ha.symm
  have h2 : Int.ModEq m (2 * b - a) (2 * a - a) := (h.mul_left 2).sub_right a
  have h3 : Int.ModEq m (3 * b - 2 * a) (3 * a - 2 * a) := (h.mul_left 3).sub_right (2 * a)
  rw [show 2 * a - a = a by ring] at h2
  rw [show 3 * a - 2 * a = a by ring] at h3
  unfold Int.ModEq at h2 h3
  exact ⟨h2.trans ha, h3.trans ha⟩

/-- **Residue-class restriction.** -/
theorem safe_filter_mod (θ : ℕ → ℤ → Bool) (Q : List ℤ) (m c : ℤ)
    (hS : Safe (treeLt θ) Q) : Safe (treeLt θ) (Q.filter (fun x => decide (x % m = c))) :=
  safe_filter (closed_mod m c) θ Q hS

/-! ### Scaling by `y ↦ 2y + c` -/

lemma div_mod_two_mul (y c : ℤ) (hc : c = 0 ∨ c = 1) (k : ℕ) :
    (2 * y + c) / 2 ^ (k + 1) = y / 2 ^ k ∧
      (2 * y + c) % 2 ^ (k + 1) = 2 * (y % 2 ^ k) + c := by
  have hM : (0 : ℤ) < 2 ^ k := by positivity
  have hp : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [hp]
  have h1 := Int.mul_ediv_add_emod y (2 ^ k)
  have h2 := Int.emod_nonneg y hM.ne'
  have h3 := Int.emod_lt_of_pos y hM
  refine (Int.ediv_emod_unique (by positivity)).2 ⟨?_, ?_, ?_⟩
  · have : 2 * (y % 2 ^ k) + c + 2 * 2 ^ k * (y / 2 ^ k) =
        2 * (2 ^ k * (y / 2 ^ k) + y % 2 ^ k) + c := by ring
    rw [this, h1]
  · rcases hc with rfl | rfl <;> linarith
  · rcases hc with rfl | rfl <;> linarith

lemma val_two_mul {d : ℤ} (hd : d ≠ 0) : padicValInt 2 (2 * d) = padicValInt 2 d + 1 := by
  rw [padicValInt.mul (by norm_num) hd]
  have : padicValInt 2 2 = 1 := by
    have := padicValInt.self (p := 2) (by norm_num); simpa using this
  rw [this]; ring

/-- The shifted witness on the subtree of residue `c` mod 2. -/
def shiftθ (θ : ℕ → ℤ → Bool) (c : ℤ) : ℕ → ℤ → Bool := fun k r => θ (k + 1) (2 * r + c)

lemma C1_map (c : ℤ) (P : List ℤ) (a b : ℤ) :
    C1 (P.map (fun y => 2 * y + c)) (2 * a + c) (2 * b + c) ↔ C1 P a b := by
  have hf : Function.Injective (fun y : ℤ => 2 * y + c) := by
    intro x y h; simp only at h; linarith
  have e2 : 2 * (2 * b + c) - (2 * a + c) = 2 * (2 * b - a) + c := by ring
  have e3 : 3 * (2 * b + c) - 2 * (2 * a + c) = 2 * (3 * b - 2 * a) + c := by ring
  unfold C1
  rw [e2, e3]
  simp only [List.mem_map_of_injective hf]
  rw [idx_map hf a, idx_map hf b, idx_map hf (2 * b - a), idx_map hf (3 * b - 2 * a)]

lemma C2_map (θ : ℕ → ℤ → Bool) (c : ℤ) (hc : c = 0 ∨ c = 1) (P : List ℤ) (a b : ℤ) :
    C2 θ (P.map (fun y => 2 * y + c)) (2 * a + c) (2 * b + c) ↔ C2 (shiftθ θ c) P a b := by
  have hf : Function.Injective (fun y : ℤ => 2 * y + c) := by
    intro x y h; simp only at h; linarith
  have e2 : 2 * (2 * b + c) - (2 * a + c) = 2 * (2 * b - a) + c := by ring
  have e3 : 3 * (2 * b + c) - 2 * (2 * a + c) = 2 * (3 * b - 2 * a) + c := by ring
  have hd : 2 * b + c - (2 * a + c) = 2 * (b - a) := by ring
  unfold C2
  rw [e2, e3, hd]
  simp only [List.mem_map_of_injective hf]
  rw [idx_map hf a, idx_map hf b]
  constructor
  · intro h ha hb i n2 n3
    have hne : b - a ≠ 0 := by
      intro h0; have : b = a := by linarith
      subst this; exact lt_irrefl _ i
    have h' := h ha hb i n2 n3
    rw [val_two_mul hne] at h'
    rw [(div_mod_two_mul a c hc _).2] at h'
    unfold bitOne at h' ⊢
    rw [(div_mod_two_mul b c hc _).1] at h'
    exact h'
  · intro h ha hb i n2 n3
    have hne : b - a ≠ 0 := by
      intro h0; have : b = a := by linarith
      subst this; exact lt_irrefl _ i
    have h' := h ha hb i n2 n3
    rw [val_two_mul hne, (div_mod_two_mul a c hc _).2]
    unfold bitOne at h' ⊢
    rw [(div_mod_two_mul b c hc _).1]
    exact h'

/-- **Scaling lemma (both directions).** For `c ∈ {0,1}`, the word `2P + c` is θ-safe iff `P`
is safe for the shifted witness `θ'(k, r) = θ(k+1, 2r + c)`. -/
theorem safe_map_iff (θ : ℕ → ℤ → Bool) (c : ℤ) (hc : c = 0 ∨ c = 1) (P : List ℤ) :
    Safe (treeLt θ) (P.map (fun y => 2 * y + c)) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + c))) P := by
  change _ ↔ Safe (treeLt (shiftθ θ c)) P
  rw [safe_iff_C, safe_iff_C]
  constructor
  · intro h a b
    exact ⟨(C1_map c P a b).1 (h _ _).1, (C2_map θ c hc P a b).1 (h _ _).2⟩
  · intro h x y
    by_cases hx : x ∈ P.map (fun y => 2 * y + c)
    · by_cases hy : y ∈ P.map (fun y => 2 * y + c)
      · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
        exact ⟨(C1_map c P a b).2 (h a b).1, (C2_map θ c hc P a b).2 (h a b).2⟩
      · exact ⟨fun _ h' => absurd h' hy, fun _ h' => absurd h' hy⟩
    · exact ⟨fun h' => absurd h' hx, fun h' => absurd h' hx⟩

lemma map_half (Q : List ℤ) (c : ℤ) (hc : c = 0 ∨ c = 1) :
    ((Q.filter (fun x => decide (x % 2 = c))).map (· / 2)).map (fun y => 2 * y + c) =
      Q.filter (fun x => decide (x % 2 = c)) := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (Q.filter _)]
  apply List.map_congr_left
  intro x hx
  have := (List.mem_filter.1 hx).2
  simp only [decide_eq_true_eq] at this
  simp only [Function.comp_apply, id]
  omega

/-- **Parity decomposition of tree safety.** A word is θ-safe iff (1) its even part halved is safe
for the shifted witness `θ(k+1, 2r)`, (2) its odd part mapped by `x ↦ (x-1)/2` is safe for
`θ(k+1, 2r+1)`, and (3) the root (odd-difference) conditions hold: every in-order pair `a, b` of
opposite parity with `2b-a` later in the word has `3b-2a` before `2b-a`, and every such pair with
neither `2b-a` nor `3b-2a` in the word has `b` odd exactly when `θ 0 0 = true`. -/
theorem safe_parity_decomp (θ : ℕ → ℤ → Bool) (Q : List ℤ) :
    Safe (treeLt θ) Q ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
          ((Q.filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
          ((Q.filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → (b - a) % 2 = 1 → Q.idxOf a < Q.idxOf b →
        (2 * b - a ∈ Q → Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
        (2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → (θ 0 0 = true ↔ b % 2 = 1))) := by
  have e0 : (fun k r => θ (k + 1) (2 * r)) = (fun k r => θ (k + 1) (2 * r + 0)) := by
    funext k r; simp
  rw [e0, ← safe_map_iff θ 0 (Or.inl rfl), ← safe_map_iff θ 1 (Or.inr rfl),
    map_half Q 0 (Or.inl rfl), map_half Q 1 (Or.inr rfl)]
  -- mixed pairs: the root conditions
  have mixed : ∀ a b : ℤ, (b - a) % 2 = 1 → (C1 Q a b ∧ C2 θ Q a b ↔
      (a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
        (2 * b - a ∈ Q → Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
        (2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → (θ 0 0 = true ↔ b % 2 = 1)))) := by
    intro a b hab
    have hv : padicValInt 2 (b - a) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro h; have := Int.emod_eq_zero_of_dvd h; omega
    have hr : a % 2 ^ 0 = 0 := by simp
    have hb : bitOne b 0 ↔ b % 2 = 1 := by unfold bitOne; simp
    unfold C1 C2
    rw [hv, hr, hb]
    constructor
    · rintro ⟨h1, h2⟩ ha hb' i
      exact ⟨fun hc i2 => h1 ha hb' hc i i2, fun n2 n3 => h2 ha hb' i n2 n3⟩
    · intro h
      exact ⟨fun ha hb' hc i i2 => (h ha hb' i).1 hc i2, fun ha hb' i n2 n3 => (h ha hb' i).2 n2 n3⟩
  rw [safe_iff_C, safe_iff_C, safe_iff_C]
  constructor
  · intro h
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b ha hb hab i => ((mixed a b hab).1 (h a b)) ha hb i⟩
    · by_cases hp : (decide (a % 2 = 0) = true ∧ decide (b % 2 = 0) = true)
      · exact ⟨(C1_filter (closed_mod 2 0) Q hp.1 hp.2).2 (h a b).1,
          (C2_filter (closed_mod 2 0) θ Q hp.1 hp.2).2 (h a b).2⟩
      · exact C_filter_vac θ Q hp
    · by_cases hp : (decide (a % 2 = 1) = true ∧ decide (b % 2 = 1) = true)
      · exact ⟨(C1_filter (closed_mod 2 1) Q hp.1 hp.2).2 (h a b).1,
          (C2_filter (closed_mod 2 1) θ Q hp.1 hp.2).2 (h a b).2⟩
      · exact C_filter_vac θ Q hp
  · rintro ⟨hE, hO, hM⟩ a b
    by_cases hab : (b - a) % 2 = 1
    · exact (mixed a b hab).2 (fun ha hb i => hM a b ha hb hab i)
    · have hab' : a % 2 = b % 2 := by omega
      rcases Int.emod_two_eq_zero_or_one a with h0 | h0
      · have hp : decide (a % 2 = 0) = true ∧ decide (b % 2 = 0) = true := by
          simp only [decide_eq_true_eq]; omega
        exact ⟨(C1_filter (closed_mod 2 0) Q hp.1 hp.2).1 (hE a b).1,
          (C2_filter (closed_mod 2 0) θ Q hp.1 hp.2).1 (hE a b).2⟩
      · have hp : decide (a % 2 = 1) = true ∧ decide (b % 2 = 1) = true := by
          simp only [decide_eq_true_eq]; omega
        exact ⟨(C1_filter (closed_mod 2 1) Q hp.1 hp.2).1 (hO a b).1,
          (C2_filter (closed_mod 2 1) θ Q hp.1 hp.2).1 (hO a b).2⟩

end E195Par

namespace E195Aff
open Erdos195 E195Tree E195Par

lemma odd_ne_zero {m : ℤ} (hm : m % 2 = 1) : m ≠ 0 := by
  rintro rfl; simp at hm

lemma val_odd_mul {m : ℤ} (hm : m % 2 = 1) {d : ℤ} (hd : d ≠ 0) :
    padicValInt 2 (m * d) = padicValInt 2 d := by
  rw [padicValInt.mul (odd_ne_zero hm) hd, padicValInt.eq_zero_of_not_dvd
    (by intro h; have := Int.emod_eq_zero_of_dvd h; omega)]
  simp

lemma aff_decomp (m s x : ℤ) (k : ℕ) :
    m * x + s = (m * (x % 2 ^ k) + s) + 2 ^ k * (m * (x / 2 ^ k)) := by
  have h := Int.mul_ediv_add_emod x (2 ^ k)
  linear_combination (-m) * h

lemma aff_mod (m s x : ℤ) (k : ℕ) : (m * x + s) % 2 ^ k = (m * (x % 2 ^ k) + s) % 2 ^ k := by
  rw [aff_decomp m s x k, Int.add_mul_emod_self_left]

lemma aff_div {m : ℤ} (hm : m % 2 = 1) (s x : ℤ) (k : ℕ) :
    (m * x + s) / 2 ^ k % 2 = (x / 2 ^ k + (m * (x % 2 ^ k) + s) / 2 ^ k) % 2 := by
  rw [aff_decomp m s x k, Int.add_mul_ediv_left _ _ (by positivity)]
  generalize (m * (x % 2 ^ k) + s) / 2 ^ k = u
  generalize x / 2 ^ k = q
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
  have : (2 * j + 1) * q = 2 * (j * q) + q := by ring
  rw [this]; omega

lemma aff_bit {m : ℤ} (hm : m % 2 = 1) (s x : ℤ) (k : ℕ) :
    bitOne (m * x + s) k ↔ (bitOne x k ↔ ¬ bitOne (m * (x % 2 ^ k) + s) k) := by
  unfold bitOne
  rw [aff_div hm]
  generalize (m * (x % 2 ^ k) + s) / 2 ^ k = u
  generalize x / 2 ^ k = q
  omega

lemma coprime_two_pow {m : ℤ} (hm : m % 2 = 1) (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) m := by
  apply IsCoprime.pow_left
  exact ⟨-(m / 2), 1, by omega⟩

lemma aff_res_inj {m : ℤ} (hm : m % 2 = 1) (s : ℤ) {k : ℕ} {r₁ r₂ : ℤ}
    (h1 : 0 ≤ r₁) (h1' : r₁ < 2 ^ k) (h2 : 0 ≤ r₂) (h2' : r₂ < 2 ^ k)
    (h : (m * r₁ + s) % 2 ^ k = (m * r₂ + s) % 2 ^ k) : r₁ = r₂ := by
  have hd : (2 : ℤ) ^ k ∣ (r₁ - r₂) * m := by
    have := (Int.ModEq.dvd h.symm)
    have e : m * r₁ + s - (m * r₂ + s) = (r₁ - r₂) * m := by ring
    rw [e] at this; exact this
  have h3 := (coprime_two_pow hm k).dvd_of_dvd_mul_right hd
  have h4 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> linarith)
  linarith

/-- Specification of the transported witness for `x ↦ m x + s`. -/
def AffSpec (θ θ' : ℕ → ℤ → Bool) (m s : ℤ) : Prop :=
  ∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
    (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))

lemma affSpec_exists (θ : ℕ → ℤ → Bool) {m : ℤ} (hm : m % 2 = 1) (s : ℤ) :
    ∃ θ', AffSpec θ θ' m s := by
  classical
  refine ⟨fun k ρ => decide (∃ r : ℤ, 0 ≤ r ∧ r < 2 ^ k ∧ (m * r + s) % 2 ^ k = ρ ∧
    (θ k r = true ↔ ¬ bitOne (m * r + s) k)), fun k r h0 h1 => ?_⟩
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨r', h0', h1', he, hp⟩
    have := aff_res_inj hm s h0' h1' h0 h1 he
    subst this; exact hp
  · intro hp; exact ⟨r, h0, h1, rfl, hp⟩

lemma aff_treeLt_iff {θ θ' : ℕ → ℤ → Bool} {m s : ℤ} (hm : m % 2 = 1)
    (hθ : AffSpec θ θ' m s) (x y : ℤ) :
    treeLt θ x y ↔ treeLt θ' (m * x + s) (m * y + s) := by
  unfold treeLt
  rw [show m * y + s - (m * x + s) = m * (y - x) by ring]
  by_cases hxy : x = y
  · subst hxy; simp
  have hd : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  rw [val_odd_mul hm hd]
  have hne : m * x + s ≠ m * y + s := by
    intro h; apply hxy
    have : m * (x - y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (odd_ne_zero hm)
    · linarith
  generalize padicValInt 2 (y - x) = k
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  have hsp := hθ k (x % 2 ^ k) (Int.emod_nonneg x hpos.ne') (Int.emod_lt_of_pos x hpos)
  rw [aff_mod m s x k, aff_bit hm s x k]
  constructor
  · rintro ⟨-, h⟩; exact ⟨hne, by tauto⟩
  · rintro ⟨-, h⟩; exact ⟨hxy, by tauto⟩

lemma aff_inj {m : ℤ} (hm : m % 2 = 1) (s : ℤ) : Function.Injective (fun x : ℤ => m * x + s) := by
  intro x y h
  simp only at h
  have : m * (x - y) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' (odd_ne_zero hm)
  · linarith

lemma APC_aff {m : ℤ} (hm : m % 2 = 1) (s : ℤ) (Q : List ℤ) :
    APC (Q.map (fun x => m * x + s)) ↔ APC Q := by
  have hf := aff_inj hm s
  have e2 : ∀ a b : ℤ, 2 * (m * b + s) - (m * a + s) = m * (2 * b - a) + s := by intros; ring
  have e3 : ∀ a b : ℤ, 3 * (m * b + s) - 2 * (m * a + s) = m * (3 * b - 2 * a) + s := by
    intros; ring
  unfold APC
  constructor
  · intro h a b ha hb hc i1 i2
    have := h (m * a + s) (m * b + s)
    rw [e2, e3] at this
    simp only [List.mem_map_of_injective hf, idx_map hf] at this
    exact this ha hb hc i1 i2
  · intro h a' b' ha hb
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    rw [e2, e3]
    simp only [List.mem_map_of_injective hf, idx_map hf] at ha hb ⊢
    exact h a b ha hb

lemma open_aff {θ θ' : ℕ → ℤ → Bool} {m s : ℤ} (hm : m % 2 = 1)
    (hθ : AffSpec θ θ' m s) (Q : List ℤ) :
    (∀ a b : ℤ, a ∈ Q.map (fun x => m * x + s) → b ∈ Q.map (fun x => m * x + s) →
      (Q.map (fun x => m * x + s)).idxOf a < (Q.map (fun x => m * x + s)).idxOf b →
      2 * b - a ∉ Q.map (fun x => m * x + s) → 3 * b - 2 * a ∉ Q.map (fun x => m * x + s) →
      ¬ treeLt θ' a b) ↔
    (∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
      2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → ¬ treeLt θ a b) := by
  have hf := aff_inj hm s
  have e2 : ∀ a b : ℤ, 2 * (m * b + s) - (m * a + s) = m * (2 * b - a) + s := by intros; ring
  have e3 : ∀ a b : ℤ, 3 * (m * b + s) - 2 * (m * a + s) = m * (3 * b - 2 * a) + s := by
    intros; ring
  constructor
  · intro h a b ha hb i n2 n3
    have := h (m * a + s) (m * b + s)
    rw [e2, e3, ← aff_treeLt_iff hm hθ] at this
    simp only [List.mem_map_of_injective hf, idx_map hf] at this
    exact this ha hb i n2 n3
  · intro h a' b' ha hb
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    rw [e2, e3, ← aff_treeLt_iff hm hθ]
    simp only [List.mem_map_of_injective hf, idx_map hf] at ha hb ⊢
    exact h a b ha hb

theorem safe_aff_iff {θ θ' : ℕ → ℤ → Bool} {m s : ℤ} (hm : m % 2 = 1)
    (hθ : AffSpec θ θ' m s) (Q : List ℤ) :
    Safe (treeLt θ) Q ↔ Safe (treeLt θ') (Q.map (fun x => m * x + s)) := by
  rw [safe_iff_conds (treeLt_no3AP θ) (treeLt_star θ),
    safe_iff_conds (treeLt_no3AP θ') (treeLt_star θ'), conds_iff, conds_iff,
    APC_aff hm s Q, open_aff hm hθ Q]

end E195Aff

namespace Erdos195
open E195Aff

/-- **Odd affine symmetry of tree safety.** For odd `m` (any sign) and any `s`, the map
`x ↦ m x + s` transports tree orders to tree orders and tree-safe words to tree-safe words, exactly:
the transported witness θ' is determined by `θ'(k, (m r + s) mod 2^k) = θ(k, r) xor bit_k(m r + s)`
for `0 ≤ r < 2^k`; such θ' exists, the map is an order isomorphism `≺_θ → ≺_θ'`, and
`Q` is θ-safe iff `m Q + s` is θ'-safe. (`m = -1` gives the mirror `x ↦ s - x`.) -/
theorem safe_odd_affine_iff (θ : ℕ → ℤ → Bool) (m s : ℤ) (hm : m % 2 = 1) :
    (∃ θ' : ℕ → ℤ → Bool, ∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
        (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))) ∧
    ∀ θ' : ℕ → ℤ → Bool, (∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
        (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))) →
      (∀ x y : ℤ, treeLt θ x y ↔ treeLt θ' (m * x + s) (m * y + s)) ∧
      (∀ Q : List ℤ, Safe (treeLt θ) Q ↔ Safe (treeLt θ') (Q.map (fun x => m * x + s))) :=
  ⟨affSpec_exists θ hm s, fun _ hθ => ⟨aff_treeLt_iff hm hθ, safe_aff_iff hm hθ⟩⟩

end Erdos195


open Erdos195 in
theorem solution (θ : ℕ → ℤ → Bool) (m s : ℤ) (hm : m % 2 = 1) :
    (∃ θ' : ℕ → ℤ → Bool, ∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
        (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))) ∧
    ∀ θ' : ℕ → ℤ → Bool, (∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
        (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))) →
      (∀ x y : ℤ, treeLt θ x y ↔ treeLt θ' (m * x + s) (m * y + s)) ∧
      (∀ Q : List ℤ, Safe (treeLt θ) Q ↔ Safe (treeLt θ') (Q.map (fun x => m * x + s))) :=
  Erdos195.safe_odd_affine_iff θ m s hm
#print axioms solution
