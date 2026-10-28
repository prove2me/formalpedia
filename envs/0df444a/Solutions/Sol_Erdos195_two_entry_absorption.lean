-- Prove2me | solution 1 for Erdos195.two_entry_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T13:50:07.270225+00:00
-- url     : https://prove2.me/submissions/354aed18-a123-47f6-83b6-25d14a69fff8

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

namespace E195W
open Erdos195 E195Tree

/-- fuelled 2-adic valuation (only used as a certificate candidate) -/
def v2f : ℕ → ℤ → ℕ
  | 0, _ => 0
  | n + 1, z => if z % 2 = 0 ∧ z ≠ 0 then v2f n (z / 2) + 1 else 0

def vv (z : ℤ) : ℕ := v2f 128 z

lemma val_eq_of_cert {z : ℤ} {k : ℕ} (h1 : z % 2 ^ k = 0) (h2 : z / 2 ^ k % 2 = 1) :
    padicValInt 2 z = k := by
  have hz : z ≠ 0 := by rintro rfl; simp at h2
  have hdk : (2 : ℤ) ^ k ∣ z := Int.dvd_of_emod_eq_zero h1
  apply le_antisymm
  · by_contra hc
    have hd : (2 : ℤ) ^ (k + 1) ∣ z := dvd_of_le_val (by omega)
    obtain ⟨m, hm⟩ := hd
    have : z / 2 ^ k = 2 * m := by
      rw [hm, pow_succ, mul_assoc, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num))]
    omega
  · exact le_val_of_dvd hz hdk

def forced (Q : List ℤ) : List (ℕ × ℤ × Bool) :=
  Q.flatMap fun a => Q.filterMap fun b =>
    if Q.idxOf a < Q.idxOf b ∧ 2 * b - a ∉ Q ∧ 3 * b - 2 * a ∉ Q then
      some (vv (b - a), a % 2 ^ (vv (b - a)), decide (b / 2 ^ (vv (b - a)) % 2 = 1)) else none

def thetaOf (Q : List ℤ) (k : ℕ) (r : ℤ) : Bool :=
  match (forced Q).find? (fun t => t.1 == k && t.2.1 == r) with
  | some t => t.2.2
  | none => false

def Good (Q : List ℤ) : Prop :=
  (∀ a ∈ Q, ∀ b ∈ Q, 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b → Q.idxOf b < Q.idxOf (2 * b - a) →
      3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
  (∀ a ∈ Q, ∀ b ∈ Q, Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
     (b - a) % 2 ^ (vv (b - a)) = 0 ∧ (b - a) / 2 ^ (vv (b - a)) % 2 = 1 ∧
     (thetaOf Q (vv (b - a)) (a % 2 ^ (vv (b - a))) = true ↔ b / 2 ^ (vv (b - a)) % 2 = 1) ∧
     ((b - a) % 2 = 1 → b % 2 = 0))

instance (Q : List ℤ) : Decidable (Good Q) := by unfold Good; infer_instance

theorem good_sound (Q : List ℤ) (h : Good Q) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ∧
    ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
      (b - a) % 2 = 1 → b % 2 = 0 := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨thetaOf Q, (treeLt_safe_iff _ Q).2 ⟨fun a b ha hb hc i1 i2 => h1 a ha b hb hc i1 i2, ?_⟩⟩, ?_⟩
  · intro a b ha hb i n2 n3
    obtain ⟨c1, c2, c3, -⟩ := h2 a ha b hb i n2 n3
    rw [val_eq_of_cert c1 c2]; exact c3
  · intro a b ha hb i n2 n3
    exact (h2 a ha b hb i n2 n3).2.2.2

end E195W


namespace E195W
open Erdos195 E195Tree

lemma val_form {z : ℤ} {k : ℕ} {m : ℤ} (h : z = 2 ^ k * (2 * m + 1)) : padicValInt 2 z = k := by
  have hp : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  apply val_eq_of_cert
  · rw [h]; exact Int.mul_emod_right _ _
  · rw [h, Int.mul_ediv_cancel_left _ hp]; omega

lemma form_of_val {z : ℤ} (hz : z ≠ 0) : ∃ m : ℤ, z = 2 ^ padicValInt 2 z * (2 * m + 1) := by
  obtain ⟨w, hw⟩ := two_pow_val_dvd z
  set v := padicValInt 2 z with hv
  refine ⟨w / 2, ?_⟩
  rcases Int.emod_two_eq_zero_or_one w with h | h
  · exfalso
    have hd : (2 : ℤ) ^ (v + 1) ∣ z := ⟨w / 2, by rw [hw, pow_succ, mul_assoc]; congr 1; omega⟩
    have := le_val_of_dvd hz hd
    omega
  · rw [hw]; congr 1; omega

lemma bit_of_form {x a : ℤ} {k : ℕ} {m : ℤ} (h : x - a = 2 ^ k * (2 * m + 1)) :
    bitOne x k ↔ ¬ bitOne a k := by
  have hp : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hx : x = a + (2 * m + 1) * 2 ^ k := by rw [mul_comm]; linarith
  unfold bitOne
  rw [hx, Int.add_mul_ediv_right _ _ hp]
  omega

lemma two_entry_le (a b y : ℤ) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (h : padicValInt 2 (y - a) ≤ padicValInt 2 (b - a)) :
    [a, b, y].Nodup ∧ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [a, b, y] := by
  obtain ⟨p, hp⟩ := form_of_val (sub_ne_zero.2 (Ne.symm hab))
  obtain ⟨q, hq⟩ := form_of_val (sub_ne_zero.2 hya)
  refine ⟨by simp [List.nodup_cons]; tauto, ?_⟩
  have i0 : [a, b, y].idxOf a = 0 := by simp
  have i1 : [a, b, y].idxOf b = 1 := by rw [List.idxOf_cons_ne _ hab]; simp
  have i2 : [a, b, y].idxOf y = 2 := by
    rw [List.idxOf_cons_ne _ (Ne.symm hya), List.idxOf_cons_ne _ (Ne.symm hyb)]; simp
  have hne : 2 * b - a ≠ y := by
    intro hc
    have := val_form (show y - a = 2 ^ (padicValInt 2 (b - a) + 1) * (2 * p + 1) by
      rw [pow_succ]; linear_combination (-1) * hc + 2 * hp)
    omega
  have F1 : padicValInt 2 (b - a) = padicValInt 2 (y - a) →
      (bitOne b (padicValInt 2 (b - a)) ↔ bitOne y (padicValInt 2 (b - a))) := by
    intro he
    rw [← he] at hq
    exact (bit_of_form hp).trans (bit_of_form hq).symm
  have F1' : padicValInt 2 (y - a) = padicValInt 2 (b - a) →
      (bitOne y (padicValInt 2 (y - a)) ↔ bitOne b (padicValInt 2 (y - a))) := by
    intro he; rw [he]; exact (F1 he.symm).symm
  have F2 : padicValInt 2 (b - a) ≠ padicValInt 2 (y - b) := by
    intro he
    obtain ⟨r, hr⟩ := form_of_val (sub_ne_zero.2 hyb)
    rw [← he] at hr
    have hd : (2 : ℤ) ^ (padicValInt 2 (b - a) + 1) ∣ y - a :=
      ⟨r + p + 1, by rw [pow_succ]; linear_combination hr + hp⟩
    have := le_val_of_dvd (sub_ne_zero.2 hya) hd
    omega
  rw [exists_treeLt_safe_iff]
  constructor
  · intro x z hx hz hc ix iz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz hc
    rcases hx with hx | hx | hx <;> subst x <;> rcases hz with hz | hz | hz <;> subst z <;>
      rcases hc with hc | hc | hc <;> rw [hc] at iz <;> first | omega | exact absurd hc hne
  · intro x z x' z' hx hz i n2 n3 hx' hz' i' n2' n3' hk hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz hx' hz'
    rcases hx with hx | hx | hx <;> subst x <;> rcases hz with hz | hz | hz <;> subst z <;>
      rcases hx' with hx' | hx' | hx' <;> subst x' <;> rcases hz' with hz' | hz' | hz' <;> subst z' <;>
      first
      | exact Iff.rfl
      | omega
      | exact F1 hk
      | exact F1' hk
      | exact absurd hk F2
      | exact absurd hk.symm F2

lemma two_entry_gt (a b y : ℤ) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (h : padicValInt 2 (b - a) < padicValInt 2 (y - a)) :
    [a, b, 2 * y - b, y].Nodup ∧ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [a, b, 2 * y - b, y] := by
  obtain ⟨p, hp⟩ := form_of_val (sub_ne_zero.2 (Ne.symm hab))
  obtain ⟨e, he⟩ := dvd_of_le_val (show padicValInt 2 (b - a) + 1 ≤ padicValInt 2 (y - a) by omega)
  set K := padicValInt 2 (b - a) with hK
  have hra : 2 * y - b ≠ a := by
    intro hc
    have hd : (2 : ℤ) ^ (K + 1) ∣ b - a := ⟨2 * e, by rw [pow_succ] at he ⊢; linear_combination 2 * he - hc⟩
    have := le_val_of_dvd (sub_ne_zero.2 (Ne.symm hab)) hd
    omega
  have hrb : 2 * y - b ≠ b := by intro hc; omega
  have hry : 2 * y - b ≠ y := by intro hc; omega
  refine ⟨by simp [List.nodup_cons]; omega, ?_⟩
  have i0 : [a, b, 2 * y - b, y].idxOf a = 0 := by simp
  have i1 : [a, b, 2 * y - b, y].idxOf b = 1 := by rw [List.idxOf_cons_ne _ hab]; simp
  have i2 : [a, b, 2 * y - b, y].idxOf (2 * y - b) = 2 := by
    rw [List.idxOf_cons_ne _ (Ne.symm hra), List.idxOf_cons_ne _ (Ne.symm hrb)]; simp
  have i3 : [a, b, 2 * y - b, y].idxOf y = 3 := by
    rw [List.idxOf_cons_ne _ (Ne.symm hya), List.idxOf_cons_ne _ (Ne.symm hyb),
      List.idxOf_cons_ne _ hry]; simp
  have hpk : (2 : ℤ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  -- r - a = 2^K (2(2e - p - 1) + 1)
  have far : (2 * y - b) - a = 2 ^ K * (2 * (2 * e - p - 1) + 1) := by
    rw [pow_succ] at he; linear_combination 2 * he - hp
  have fbr : (2 * y - b) - b = 2 ^ (K + 1) * (2 * (e - p - 1) + 1) := by
    rw [pow_succ] at he ⊢; linear_combination 2 * he - 2 * hp
  have Var : padicValInt 2 ((2 * y - b) - a) = K := val_form far
  have Vbr : padicValInt 2 ((2 * y - b) - b) = K + 1 := val_form fbr
  have G1 : bitOne b K ↔ bitOne (2 * y - b) K := (bit_of_form hp).trans (bit_of_form far).symm
  have G1' : bitOne (2 * y - b) (padicValInt 2 ((2 * y - b) - a)) ↔
      bitOne b (padicValInt 2 ((2 * y - b) - a)) := by rw [Var]; exact G1.symm
  have R1 : a % 2 ^ (K + 1) ≠ b % 2 ^ (K + 1) := by
    intro hc
    have hd : (2 : ℤ) ^ (K + 1) ∣ b - a := Int.ModEq.dvd hc
    have := le_val_of_dvd (sub_ne_zero.2 (Ne.symm hab)) hd
    omega
  have hne1 : 2 * b - a ≠ 2 * y - b := by
    intro hc
    have : 2 ^ K * (4 * e) = 2 ^ K * (3 * (2 * p + 1)) := by
      rw [pow_succ] at he; linear_combination (-2) * he + 3 * hp - hc
    have := mul_left_cancel₀ hpk this
    omega
  have hne3 : 2 * (2 * y - b) - b ≠ y := by intro hc; omega
  have T1 : 2 * b - a = y → 3 * b - 2 * a ∈ [a, b, 2 * y - b, y] ∧
      [a, b, 2 * y - b, y].idxOf (3 * b - 2 * a) < [a, b, 2 * y - b, y].idxOf (2 * b - a) := by
    intro hc
    have e1 : 3 * b - 2 * a = 2 * y - b := by omega
    rw [e1, hc, i2, i3]; simp
  have T2 : 2 * (2 * y - b) - a = y → 3 * (2 * y - b) - 2 * a ∈ [a, b, 2 * y - b, y] ∧
      [a, b, 2 * y - b, y].idxOf (3 * (2 * y - b) - 2 * a) <
        [a, b, 2 * y - b, y].idxOf (2 * (2 * y - b) - a) := by
    intro hc
    have e1 : 3 * (2 * y - b) - 2 * a = b := by omega
    rw [e1, hc, i1, i3]; simp
  have Cb : 2 * y - b ∈ [a, b, 2 * y - b, y] := by simp
  have Cr : 2 * y - (2 * y - b) ∈ [a, b, 2 * y - b, y] := by simp
  rw [exists_treeLt_safe_iff]
  constructor
  · intro x z hx hz hc ix iz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz hc
    rcases hx with hx | hx | hx | hx <;> subst x <;> rcases hz with hz | hz | hz | hz <;> subst z <;>
      rcases hc with hc | hc | hc | hc <;> rw [hc] at iz <;>
      first | omega | exact absurd hc hne1 | exact absurd hc hne3 | exact T1 hc | exact T2 hc
  · intro x z x' z' hx hz i n2 n3 hx' hz' i' n2' n3' hk hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz hx' hz'
    rcases hx with hx | hx | hx | hx <;> subst x <;> rcases hz with hz | hz | hz | hz <;> subst z <;>
      rcases hx' with hx' | hx' | hx' | hx' <;> subst x' <;>
      rcases hz' with hz' | hz' | hz' | hz' <;> subst z' <;>
      first
      | exact Iff.rfl
      | exact absurd Cb n2
      | exact absurd Cb n2'
      | exact absurd Cr n2
      | exact absurd Cr n2'
      | omega
      | exact G1
      | exact G1'
      | (rw [hk, Vbr] at hr; exact absurd hr R1)
      | (rw [Vbr] at hr; exact absurd hr.symm R1)

end E195W

namespace Erdos195
open E195W E195Tree

/-- **Two-entry target-last absorption (Astra).** -/
theorem two_entry_absorption (a b y : ℤ) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    let W : List ℤ := if padicValInt 2 (y - a) ≤ padicValInt 2 (b - a) then [a, b, y]
      else [a, b, 2 * y - b, y]
    W.Nodup ∧ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) W := by
  intro W
  by_cases h : padicValInt 2 (y - a) ≤ padicValInt 2 (b - a)
  · simp only [W, if_pos h]; exact two_entry_le a b y hab hya hyb h
  · simp only [W, if_neg h]; exact two_entry_gt a b y hab hya hyb (by omega)

end Erdos195


open Erdos195 in
theorem solution (a b y : ℤ) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    let W : List ℤ := if padicValInt 2 (y - a) ≤ padicValInt 2 (b - a) then [a, b, y]
      else [a, b, 2 * y - b, y]
    W.Nodup ∧ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) W := by
  first
  | exact Erdos195.two_entry_absorption
  | (apply Erdos195.two_entry_absorption <;> assumption)

#print axioms solution
