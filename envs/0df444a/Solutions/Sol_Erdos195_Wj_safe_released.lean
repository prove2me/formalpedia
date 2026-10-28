-- Prove2me | solution 1 for Erdos195.Wj_safe_released
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T10:01:41.707002+00:00
-- url     : https://prove2.me/submissions/d521b0fc-e2d3-4524-a819-11dbf6f307fc

import Mathlib
import Definitions.Def_Erdos195_tree
import Definitions.Def_Erdos195_Wj


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

lemma val_two_pow_mul_odd (k : ℕ) {o : ℤ} (ho : Odd o) : padicValInt 2 (2 ^ k * o) = k := by
  obtain ⟨m, rfl⟩ := ho
  apply val_eq_of_cert
  · rw [Int.mul_emod_right]
  · rw [Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num))]; omega

lemma nine_two_pow (r : ℕ) : ∃ w : ℤ, Odd w ∧ (9 : ℤ) ^ (2 ^ r) = 1 + 2 ^ (r + 3) * w := by
  induction r with
  | zero => exact ⟨1, odd_one, by norm_num⟩
  | succ r ih =>
    obtain ⟨w, hw, h⟩ := ih
    refine ⟨w + 2 ^ (r + 2) * w ^ 2, ?_, ?_⟩
    · have : Even ((2:ℤ) ^ (r + 2) * w ^ 2) := by
        rw [pow_succ]; exact ⟨2 ^ (r+1) * w ^ 2, by ring⟩
      exact hw.add_even this
    · rw [pow_succ, pow_mul, h]; ring

lemma one_add_pow (k s : ℕ) (hk : 1 ≤ k) (w : ℤ) :
    ∃ z : ℤ, (1 + 2 ^ k * w) ^ s = 1 + (s : ℤ) * 2 ^ k * w + 2 ^ (k + 1) * z := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨(s : ℤ) * 2 ^ (k - 1) * w ^ 2 + z * (1 + 2 ^ k * w), ?_⟩
    have e : (2 : ℤ) ^ k * 2 ^ k = 2 ^ (k + 1) * 2 ^ (k - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [pow_succ, hz]; push_cast
    linear_combination (↑s * w ^ 2) * e

/-- `9^(2^r * s) = 1 + 2^(r+3) * (s * w) + 2^(r+4) * z` with `w` odd. -/
lemma nine_pow_expand (r s : ℕ) : ∃ w z : ℤ, Odd w ∧
    (9 : ℤ) ^ (2 ^ r * s) = 1 + 2 ^ (r + 3) * ((s : ℤ) * w) + 2 ^ (r + 4) * z := by
  obtain ⟨w, hw, h⟩ := nine_two_pow r
  obtain ⟨z, hz⟩ := one_add_pow (r + 3) s (by omega) w
  exact ⟨w, z, hw, by rw [pow_mul, h, hz]; ring⟩

/-- **Lifting identity.** For odd `c`, `q = t mod 2^r`:
`bit_{r+3}(c·9^t) = bit_{r+3}(c·9^q) xor bit_r(t)`. -/
theorem lift_bit (c : ℤ) (hc : Odd c) (r t : ℕ) :
    c * 9 ^ t / 2 ^ (r + 3) % 2 = (c * 9 ^ (t % 2 ^ r) / 2 ^ (r + 3) + (t / 2 ^ r : ℕ)) % 2 := by
  obtain ⟨w, z, hw, h⟩ := nine_pow_expand r (t / 2 ^ r)
  have ht : t = t % 2 ^ r + 2 ^ r * (t / 2 ^ r) := (Nat.mod_add_div t (2 ^ r)).symm
  set q := t % 2 ^ r
  set s := t / 2 ^ r
  have hX : c * 9 ^ t = c * 9 ^ q + (s * (c * 9 ^ q * w)) * 2 ^ (r + 3)
      + (2 * (c * 9 ^ q * z)) * 2 ^ (r + 3) := by
    rw [ht, pow_add, h]; ring
  have h0 : (2 : ℤ) ^ (r + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hX, Int.add_mul_ediv_right _ _ h0, Int.add_mul_ediv_right _ _ h0]
  have ho : Odd (c * 9 ^ q * w) := (hc.mul (Odd.pow (by decide))).mul hw
  obtain ⟨o, ho⟩ := ho
  rw [ho]
  have : ((s : ℤ) * (2 * o + 1)) % 2 = (s : ℤ) % 2 := by
    rw [Int.mul_emod]; have : (2 * o + 1) % 2 = 1 := by omega
    rw [this, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
  omega

lemma nine_pow_sub_one (d : ℕ) (hd : d ≠ 0) :
    padicValInt 2 ((9 : ℤ) ^ d - 1) = 3 + padicValInt 2 (d : ℤ) := by
  obtain ⟨v, s, hs, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd
  obtain ⟨w, z, hw, h⟩ := nine_pow_expand v s
  have hs' : Odd (s : ℤ) := by exact_mod_cast hs
  have e : (9 : ℤ) ^ (2 ^ v * s) - 1 = 2 ^ (v + 3) * ((s : ℤ) * w + 2 * z) := by
    rw [h]; ring
  have e2 : ((2 ^ v * s : ℕ) : ℤ) = 2 ^ v * (s : ℤ) := by push_cast; ring
  rw [e, e2, val_two_pow_mul_odd _ ((hs'.mul hw).add_even (even_two_mul z)),
    val_two_pow_mul_odd _ hs']
  ring

/-- **ν₂(9^a − 9^b) = 3 + ν₂(a − b)** for `a ≠ b`. -/
theorem nu2_nine_pow_sub (a b : ℕ) (h : a ≠ b) :
    padicValInt 2 ((9 : ℤ) ^ a - 9 ^ b) = 3 + padicValInt 2 ((a : ℤ) - b) := by
  have key : ∀ a b : ℕ, b < a →
      padicValInt 2 ((9 : ℤ) ^ a - 9 ^ b) = 3 + padicValInt 2 ((a : ℤ) - b) := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have e : (9 : ℤ) ^ (b + d + 1) - 9 ^ b = 9 ^ b * (9 ^ (d + 1) - 1) := by ring
    have h9 : (9 : ℤ) ^ (d + 1) - 1 ≠ 0 := by
      have : (1 : ℤ) < 9 ^ (d + 1) := one_lt_pow₀ (by norm_num) (by omega)
      omega
    rw [e, padicValInt.mul (pow_ne_zero _ (by norm_num)) h9,
      padicValInt.eq_zero_of_not_dvd (by
        intro h2; have := (Int.Prime.dvd_pow' (p := 2) (by norm_num) h2); omega),
      nine_pow_sub_one _ (by omega)]
    push_cast; ring_nf
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have := key b a hlt
    rw [← padicValInt_sub_comm, this, padicValInt_sub_comm]
  · exact key a b hgt

end E195W

namespace E195W
open Erdos195 E195Tree

lemma br_succ (n p : ℕ) : br (n + 1) p = 2 * br n (p % 2 ^ n) + p / 2 ^ n := rfl

lemma top_bit {n p : ℕ} (h : p < 2 ^ (n + 1)) : p / 2 ^ n < 2 := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at h; linarith

lemma mod_two_mul (B d M : ℕ) (hd : d < 2) (hM : 0 < M) : (2 * B + d) % (2 * M) = 2 * (B % M) + d := by
  have h1 := Nat.div_add_mod B M; have h2 := Nat.mod_lt B hM
  have e : 2 * B + d = (2 * (B % M) + d) + (2 * M) * (B / M) := by
    calc 2 * B + d = 2 * (M * (B / M) + B % M) + d := by rw [h1]
      _ = _ := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma div_two_mul (B d M : ℕ) (hd : d < 2) : (2 * B + d) / (2 * M) = B / M := by
  rw [← Nat.div_div_eq_div_mul]; congr 1; omega

lemma br_lt (n p : ℕ) : br n p < 2 ^ n ∨ 2 ^ n ≤ p := by
  induction n generalizing p with
  | zero => simp [br]
  | succ n ih =>
    by_cases h : p < 2 ^ (n + 1)
    · left
      rw [br_succ, pow_succ]
      have := (ih (p % 2 ^ n)).resolve_right (by have := Nat.mod_lt p (show 0 < 2 ^ n by positivity); omega)
      have := top_bit h
      omega
    · right; omega

lemma br_lt' {n p : ℕ} (h : p < 2 ^ n) : br n p < 2 ^ n := (br_lt n p).resolve_right (by omega)

lemma br_inj (n p p' : ℕ) (h : p < 2 ^ n) (h' : p' < 2 ^ n) (e : br n p = br n p') : p = p' := by
  induction n generalizing p p' with
  | zero => simp at h h'; omega
  | succ n ih =>
    rw [br_succ, br_succ] at e
    have t1 := top_bit h; have t2 := top_bit h'
    have hd : p / 2 ^ n = p' / 2 ^ n := by
      generalize p / 2 ^ n = c at *; generalize p' / 2 ^ n = c' at *; omega
    have hm := ih (p % 2 ^ n) (p' % 2 ^ n) (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
      (by rw [hd] at e; omega)
    rw [← Nat.div_add_mod p (2 ^ n), ← Nat.div_add_mod p' (2 ^ n), hd, hm]

lemma br_zero (n : ℕ) : br n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [br_succ, ih]

lemma br_top (n : ℕ) : br n (2 ^ n - 1) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [br_succ]
    have hp : 0 < 2 ^ n := by positivity
    have e0 : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + 2 ^ n * 1 := by rw [pow_succ]; omega
    have e1 : (2 ^ (n + 1) - 1) % 2 ^ n = 2 ^ n - 1 := by
      rw [e0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (2 ^ (n + 1) - 1) / 2 ^ n = 1 := by
      rw [e0, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega)]
    rw [e1, e2, ih, pow_succ]; omega

lemma br_half (n : ℕ) : br (n + 1) (2 ^ n) = 1 := by
  rw [br_succ, Nat.mod_self, br_zero, Nat.div_self (by positivity)]

lemma br_surj (n t : ℕ) (ht : t < 2 ^ n) : ∃ p < 2 ^ n, br n p = t := by
  let g : Fin (2 ^ n) → Fin (2 ^ n) := fun p => ⟨br n p, br_lt' p.2⟩
  have hg : Function.Injective g := fun a b hab => Fin.ext (br_inj n a b a.2 b.2 (by
    simpa [g] using congrArg Fin.val hab))
  obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.1 hg) ⟨t, ht⟩
  exact ⟨p, p.2, by simpa [g] using congrArg Fin.val hp⟩

/-- **Bit-reversal MSB lemma.** If `br p`, `br p'` agree below bit `r` and differ at bit `r`,
then `p < p'` iff bit `r` of `br p'` is `1`. -/
lemma br_msb (n p p' r : ℕ) (h : p < 2 ^ n) (h' : p' < 2 ^ n)
    (hm : br n p % 2 ^ r = br n p' % 2 ^ r) (hb : br n p / 2 ^ r % 2 ≠ br n p' / 2 ^ r % 2) :
    (p < p' ↔ br n p' / 2 ^ r % 2 = 1) := by
  induction n generalizing p p' r with
  | zero => simp at h h'; subst h; subst h'; exact absurd rfl hb
  | succ n ih =>
    have t1 := top_bit h; have t2 := top_bit h'
    have l1 := Nat.mod_lt p (show 0 < 2 ^ n by positivity)
    have l2 := Nat.mod_lt p' (show 0 < 2 ^ n by positivity)
    have dp := Nat.div_add_mod p (2 ^ n); have dp' := Nat.div_add_mod p' (2 ^ n)
    have IH := fun r hm hb => ih (p % 2 ^ n) (p' % 2 ^ n) r l1 l2 hm hb
    rw [br_succ, br_succ] at hm hb; rw [br_succ]
    generalize br n (p % 2 ^ n) = A at *
    generalize br n (p' % 2 ^ n) = A' at *
    generalize p / 2 ^ n = c at *; generalize p' / 2 ^ n = c' at *
    generalize p % 2 ^ n = u at *; generalize p' % 2 ^ n = u' at *
    clear ih h h'
    generalize 2 ^ n = M at *
    cases r with
    | zero =>
      simp only [pow_zero, Nat.div_one] at hb ⊢
      interval_cases c <;> interval_cases c' <;> simp at dp dp' <;> omega
    | succ r =>
      rw [pow_succ, mul_comm (2 ^ r) 2, mod_two_mul _ _ _ t1 (by positivity),
        mod_two_mul _ _ _ t2 (by positivity)] at hm
      rw [pow_succ, mul_comm (2 ^ r) 2, div_two_mul _ _ _ t1, div_two_mul _ _ _ t2] at hb
      rw [pow_succ, mul_comm (2 ^ r) 2, div_two_mul _ _ _ t2]
      have hm' : A % 2 ^ r = A' % 2 ^ r := by omega
      have hcc : c = c' := by omega
      rw [← IH r hm' hb]
      subst hcc
      interval_cases c <;> simp at dp dp' <;> omega

end E195W

namespace E195W
open Erdos195 E195Tree

example : Wj 2 = [0, 1, 81, 9, 27, 3, 486, 243] := by decide
example : Wj 3 = [0, 1, 6561, 81, 531441, 9, 59049, 729, 177147, 27, 2187, 19683, 3, 243,
    3188646, 1594323] := by decide

lemma pow3_inj {a b : ℕ} (h : (3 : ℤ) ^ a = 3 ^ b) : a = b :=
  Int.pow_right_injective (by decide) h

lemma pow3_odd (a : ℕ) : (3 : ℤ) ^ a % 2 = 1 := by
  have : Odd ((3 : ℤ) ^ a) := Odd.pow (by decide)
  obtain ⟨k, hk⟩ := this; omega

lemma pow3_ne_two_mul (a b : ℕ) : (3 : ℤ) ^ a ≠ 2 * 3 ^ b := by
  have := pow3_odd a; omega

lemma pow3_ne_zero (a : ℕ) : (3 : ℤ) ^ a ≠ 0 := pow_ne_zero _ (by norm_num)

lemma nine_pow_mod8 (t : ℕ) : (3 : ℤ) ^ (2 * t) % 8 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih => rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_add, Int.mul_emod, ih]; norm_num

lemma pow3_mod8 (e : ℕ) : (3 : ℤ) ^ e % 8 = if e % 2 = 0 then 1 else 3 := by
  rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
  · simp [nine_pow_mod8]
  · rw [pow_succ, Int.mul_emod, nine_pow_mod8]; simp

section
variable {n : ℕ}

lemma j_ge (hn : 2 ≤ n) : 4 ≤ 2 ^ n := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

lemma half_eq (hn : 2 ≤ n) : 2 ^ n / 2 = 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [pow_succ]

lemma br_half' (hn : 2 ≤ n) : br n (2 ^ n / 2) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [half_eq hn]; simpa using br_half k

/-- Odd-block exponent index. -/
lemma odd_idx (hn : 2 ≤ n) {p : ℕ} (hp : p < 2 ^ n) (h0 : p ≠ 0) (h1 : p ≠ 2 ^ n / 2) :
    2 ≤ br n p ∧ (br n p + 2 ^ n - 2) % 2 ^ n = br n p - 2 := by
  have hl := br_lt' hp
  have a0 : br n p ≠ 0 := fun h => h0 (br_inj n p 0 hp (by positivity) (by rw [h, br_zero]))
  have a1 : br n p ≠ 1 := fun h => h1 (br_inj n p _ hp (by have := j_ge hn; omega)
    (by rw [h, br_half' hn]))
  refine ⟨by omega, ?_⟩
  have : br n p + 2 ^ n - 2 = (br n p - 2) + 2 ^ n * 1 := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma even_idx (hn : 2 ≤ n) {p : ℕ} (hp : p < 2 ^ n - 1) : br n p ≤ 2 ^ n - 2 := by
  have h1 : p < 2 ^ n := by omega
  have hl := br_lt' h1
  have : br n p ≠ 2 ^ n - 1 := fun h => by
    have := br_inj n p (2 ^ n - 1) h1 (by have := j_ge hn; omega) (by rw [h, br_top])
    omega
  omega

/-- Members of `W_j`. -/
lemma mem_Wj (hn : 2 ≤ n) {x : ℤ} (hx : x ∈ Wj n) :
    x = 0 ∨ x = 2 * 3 ^ (2 * 2 ^ n - 3) ∨ ∃ e ≤ 2 * 2 ^ n - 3, x = 3 ^ e := by
  have hj := j_ge hn
  simp only [Wj, List.mem_append, List.mem_map, List.mem_range, List.mem_filter, List.mem_reverse,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hx
  rcases hx with ((rfl | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, h0, h1⟩, rfl⟩) | rfl | rfl
  · left; rfl
  · right; right; exact ⟨_, by have := even_idx hn hp; omega, rfl⟩
  · right; right
    obtain ⟨a, b⟩ := odd_idx hn hp h0 h1
    have := br_lt' hp
    exact ⟨_, by rw [b]; omega, rfl⟩
  · right; left; rfl
  · right; right; exact ⟨_, le_refl _, rfl⟩

lemma zero_mem : (0 : ℤ) ∈ Wj n := by simp [Wj]

lemma G_mem : (2 * 3 ^ (2 * 2 ^ n - 3) : ℤ) ∈ Wj n := by simp [Wj]

lemma pow_mem (hn : 2 ≤ n) {e : ℕ} (he : e ≤ 2 * 2 ^ n - 3) : (3 : ℤ) ^ e ∈ Wj n := by
  have hj := j_ge hn
  simp only [Wj, List.mem_append, List.mem_map, List.mem_range, List.mem_filter, List.mem_reverse,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
  rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
  · left; left; right
    obtain ⟨p, hp, hb⟩ := br_surj n t (by omega)
    refine ⟨p, ?_, by rw [hb]⟩
    by_contra hc
    have : p = 2 ^ n - 1 := by omega
    rw [this, br_top] at hb; omega
  · by_cases ht : t = 2 ^ n - 2
    · right; right; subst ht; congr 1; omega
    · left; right
      obtain ⟨p, hp, hb⟩ := br_surj n (t + 2) (by omega)
      have h0 : p ≠ 0 := by rintro rfl; rw [br_zero] at hb; omega
      have h1 : p ≠ 2 ^ n / 2 := by rintro rfl; rw [br_half' hn] at hb; omega
      refine ⟨p, ⟨hp, h0, h1⟩, ?_⟩
      rw [(odd_idx hn hp h0 h1).2, hb]; congr 2

lemma not_mem_pow (hn : 2 ≤ n) {e : ℕ} (he : 2 * 2 ^ n - 3 < e) : (3 : ℤ) ^ e ∉ Wj n := by
  intro h
  rcases mem_Wj hn h with h | h | ⟨e', he', h⟩
  · exact pow3_ne_zero _ h
  · exact pow3_ne_two_mul _ _ h
  · have := pow3_inj h; omega

lemma not_mem_two_pow (hn : 2 ≤ n) {e : ℕ} (he : e ≠ 2 * 2 ^ n - 3) : 2 * (3 : ℤ) ^ e ∉ Wj n := by
  intro h
  rcases mem_Wj hn h with h | h | ⟨e', he', h⟩
  · have := pow3_ne_zero e; omega
  · exact he (pow3_inj (by linarith))
  · exact pow3_ne_two_mul _ _ h.symm

end
end E195W

namespace E195W
open Erdos195 E195Tree

lemma bitOne_nat (x r : ℕ) : bitOne (x : ℤ) r ↔ x / 2 ^ r % 2 = 1 := by
  unfold bitOne
  have : ((x / 2 ^ r % 2 : ℕ) : ℤ) = (x : ℤ) / 2 ^ r % 2 := by push_cast; rfl
  constructor
  · intro h; exact_mod_cast this.trans h
  · intro h; rw [← this, h]; rfl

lemma nat_digits {x y : ℕ} (h : x ≠ y) :
    x % 2 ^ padicValInt 2 ((y : ℤ) - x) = y % 2 ^ padicValInt 2 ((y : ℤ) - x) ∧
    x / 2 ^ padicValInt 2 ((y : ℤ) - x) % 2 ≠ y / 2 ^ padicValInt 2 ((y : ℤ) - x) % 2 := by
  set r := padicValInt 2 ((y : ℤ) - x)
  have hne : (x : ℤ) ≠ y := by exact_mod_cast h
  have h1 := emod_eq_of_dvd (two_pow_val_dvd ((y : ℤ) - x))
  have h2 := digit_ne hne
  have c1 : ((x % 2 ^ r : ℕ) : ℤ) = (x : ℤ) % 2 ^ r := by push_cast; rfl
  have c2 : ((y % 2 ^ r : ℕ) : ℤ) = (y : ℤ) % 2 ^ r := by push_cast; rfl
  have c3 : ((x / 2 ^ r % 2 : ℕ) : ℤ) = (x : ℤ) / 2 ^ r % 2 := by push_cast; rfl
  have c4 : ((y / 2 ^ r % 2 : ℕ) : ℤ) = (y : ℤ) / 2 ^ r % 2 := by push_cast; rfl
  refine ⟨by exact_mod_cast c1.trans (h1.trans c2.symm), ?_⟩
  rw [← c3, ← c4] at h2
  have := Nat.mod_lt (x / 2 ^ r) (show 0 < 2 by norm_num)
  have := Nat.mod_lt (y / 2 ^ r) (show 0 < 2 by norm_num)
  omega

/-- order data for two powers `3^u` before `3^v` -/
def OrdExp (u v : ℕ) : Prop :=
  (u % 2 = 1 → v % 2 = 1) ∧
  (u % 2 = 0 → v % 2 = 0 →
    bitOne ((v / 2 : ℕ) : ℤ) (padicValInt 2 (((v / 2 : ℕ) : ℤ) - ((u / 2 : ℕ) : ℤ)))) ∧
  (u % 2 = 1 → v % 2 = 1 →
    ¬ bitOne ((v / 2 + 2 : ℕ) : ℤ) (padicValInt 2 (((v / 2 : ℕ) : ℤ) - ((u / 2 : ℕ) : ℤ))))

def Rel (n : ℕ) (x y : ℤ) : Prop :=
  y ≠ 0 ∧ x ≠ 3 ^ (2 * 2 ^ n - 3) ∧ (x = 2 * 3 ^ (2 * 2 ^ n - 3) → y = 3 ^ (2 * 2 ^ n - 3)) ∧
  ∀ u v : ℕ, x = 3 ^ u → y = 3 ^ v → u ≠ v → OrdExp u v

section
variable {n : ℕ}

lemma rel_zero {y : ℤ} (hy : y ≠ 0) : Rel n 0 y :=
  ⟨hy, (pow3_ne_zero _).symm, fun h => absurd h (by have := pow3_ne_zero (2 * 2 ^ n - 3); omega),
    fun u _ hu => absurd hu.symm (pow3_ne_zero u)⟩

lemma rel_EO (hn : 2 ≤ n) (a b : ℕ) : Rel n (3 ^ (2 * a)) (3 ^ (2 * b + 1)) := by
  have := j_ge hn
  refine ⟨pow3_ne_zero _, fun h => ?_, fun h => absurd h (pow3_ne_two_mul _ _), ?_⟩
  · have := pow3_inj h; omega
  · intro u v hu hv _
    have := pow3_inj hu; have := pow3_inj hv; subst u; subst v
    refine ⟨fun h => by omega, fun _ h => by omega, fun h => by omega⟩

lemma rel_EG (hn : 2 ≤ n) (a : ℕ) : Rel n (3 ^ (2 * a)) (2 * 3 ^ (2 * 2 ^ n - 3)) := by
  have := j_ge hn
  refine ⟨by have := pow3_ne_zero (2 * 2 ^ n - 3); omega, fun h => ?_,
    fun h => absurd h (pow3_ne_two_mul _ _), ?_⟩
  · have := pow3_inj h; omega
  · intro u v _ hv; exact absurd hv.symm (pow3_ne_two_mul _ _)

lemma rel_OG (s : ℕ) (hs : 2 * s + 1 ≠ 2 * 2 ^ n - 3) :
    Rel n (3 ^ (2 * s + 1)) (2 * 3 ^ (2 * 2 ^ n - 3)) := by
  refine ⟨by have := pow3_ne_zero (2 * 2 ^ n - 3); omega, fun h => hs (pow3_inj h),
    fun h => absurd h (pow3_ne_two_mul _ _), ?_⟩
  intro u v _ hv; exact absurd hv.symm (pow3_ne_two_mul _ _)

lemma rel_GT : Rel n (2 * 3 ^ (2 * 2 ^ n - 3)) (3 ^ (2 * 2 ^ n - 3)) := by
  refine ⟨pow3_ne_zero _, fun h => pow3_ne_two_mul _ _ h.symm, fun _ => rfl, ?_⟩
  intro u v hu; exact absurd hu (pow3_ne_two_mul _ _).symm

lemma rel_EE {p p' : ℕ} (hp' : p' < 2 ^ n - 1) (hlt : p < p') :
    Rel n (3 ^ (2 * br n p)) (3 ^ (2 * br n p')) := by
  refine ⟨pow3_ne_zero _, fun h => ?_, fun h => absurd h (pow3_ne_two_mul _ _), ?_⟩
  · have := pow3_inj h; omega
  · intro u v hu hv huv
    have := pow3_inj hu; have := pow3_inj hv; subst u; subst v
    refine ⟨fun h => by omega, fun _ _ => ?_, fun h => by omega⟩
    have e1 : 2 * br n p / 2 = br n p := by omega
    have e2 : 2 * br n p' / 2 = br n p' := by omega
    rw [e1, e2, bitOne_nat]
    have hne : br n p ≠ br n p' := by omega
    obtain ⟨hm, hb⟩ := nat_digits hne
    exact (br_msb n p p' _ (by omega) (by omega) hm hb).1 hlt

lemma rel_OO (hn : 2 ≤ n) {p p' : ℕ} (hp : p < 2 ^ n) (h0 : p ≠ 0) (h1 : p ≠ 2 ^ n / 2)
    (hp' : p' < 2 ^ n) (h0' : p' ≠ 0) (h1' : p' ≠ 2 ^ n / 2) (hlt : p' < p) :
    Rel n (3 ^ (2 * ((br n p + 2 ^ n - 2) % 2 ^ n) + 1))
      (3 ^ (2 * ((br n p' + 2 ^ n - 2) % 2 ^ n) + 1)) := by
  obtain ⟨a1, a2⟩ := odd_idx hn hp h0 h1
  obtain ⟨b1, b2⟩ := odd_idx hn hp' h0' h1'
  have l1 := br_lt' hp; have l2 := br_lt' hp'
  rw [a2, b2]
  refine ⟨pow3_ne_zero _, fun h => ?_, fun h => absurd h (pow3_ne_two_mul _ _), ?_⟩
  · have := pow3_inj h; omega
  · intro u v hu hv huv
    have := pow3_inj hu; have := pow3_inj hv; subst u; subst v
    refine ⟨fun _ => by omega, fun h => by omega, fun _ _ => ?_⟩
    have e1 : (2 * (br n p - 2) + 1) / 2 = br n p - 2 := by omega
    have e2 : (2 * (br n p' - 2) + 1) / 2 + 2 = br n p' := by omega
    have e3 : (((br n p' - 2 : ℕ)) : ℤ) - ((br n p - 2 : ℕ) : ℤ) = (br n p' : ℤ) - (br n p : ℤ) := by
      omega
    rw [e1, e2, show (2 * (br n p' - 2) + 1) / 2 = br n p' - 2 by omega, e3, bitOne_nat]
    have hne : br n p' ≠ br n p := by omega
    obtain ⟨hm, hb⟩ := nat_digits hne
    rw [padicValInt_sub_comm] at hm hb
    have := (br_msb n p' p _ hp' hp hm hb).1 hlt
    omega

lemma rel_OT (hn : 2 ≤ n) {s : ℕ} (hs : s ≤ 2 ^ n - 3) :
    Rel n (3 ^ (2 * s + 1)) (3 ^ (2 * 2 ^ n - 3)) := by
  have hj := j_ge hn
  refine ⟨pow3_ne_zero _, fun h => ?_, fun h => absurd h (pow3_ne_two_mul _ _), ?_⟩
  · have := pow3_inj h; omega
  · intro u v hu hv huv
    have := pow3_inj hu; have := pow3_inj hv; subst u; subst v
    refine ⟨fun _ => by omega, fun h => by omega, fun _ _ => ?_⟩
    have e1 : (2 * s + 1) / 2 = s := by omega
    have e2 : (2 * 2 ^ n - 3) / 2 = 2 ^ n - 2 := by omega
    have e3 : 2 ^ n - 2 + 2 = 2 ^ n := by omega
    rw [e1, e2, e3, bitOne_nat]
    set r := padicValInt 2 (((2 ^ n - 2 : ℕ) : ℤ) - (s : ℤ))
    have hd0 : ((2 ^ n - 2 : ℕ) : ℤ) - (s : ℤ) ≠ 0 := by omega
    have hrn : r < n := by
      by_contra hc
      have hdv : (2 : ℤ) ^ n ∣ ((2 ^ n - 2 : ℕ) : ℤ) - (s : ℤ) := dvd_of_le_val (by omega)
      have hpos : (0 : ℤ) < ((2 ^ n - 2 : ℕ) : ℤ) - (s : ℤ) := by omega
      have := Int.le_of_dvd hpos hdv
      have : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; rfl
      omega
    have : 2 ^ n / 2 ^ r = 2 * 2 ^ (n - r - 1) := by
      rw [show n = r + (n - r - 1) + 1 by omega, pow_succ, pow_add, Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (by positivity)]
      rw [show r + (n - r - 1) + 1 - r - 1 = n - r - 1 by omega]; ring
    rw [this]; omega

lemma rel_of_idx {R : ℤ → ℤ → Prop} {L : List ℤ} (hL : L.Pairwise R) {a b : ℤ} (ha : a ∈ L)
    (hb : b ∈ L) (h : L.idxOf a < L.idxOf b) : R a b := by
  induction L with
  | nil => simp at ha
  | cons c l ih =>
    rw [List.pairwise_cons] at hL
    by_cases hac : a = c
    · subst hac
      have hbc : b ≠ a := by rintro rfl; omega
      exact hL.1 b (by simpa [hbc] using hb)
    · have hbc : b ≠ c := by
        rintro rfl; rw [List.idxOf_cons_self] at h; omega
      rw [List.idxOf_cons_ne _ (Ne.symm hac), List.idxOf_cons_ne _ (Ne.symm hbc)] at h
      exact ih hL.2 (by simpa [hac] using ha) (by simpa [hbc] using hb) (by omega)

theorem Wj_pairwise (hn : 2 ≤ n) : (Wj n).Pairwise (Rel n) := by
  have hj := j_ge hn
  have hT : 2 * 2 ^ n - 3 = 2 * (2 ^ n - 2) + 1 := by omega
  have hE : ((List.range (2 ^ n - 1)).map (fun p => (3 : ℤ) ^ (2 * br n p))).Pairwise (Rel n) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem (fun _ hb hab => rel_EE (List.mem_range.1 hb) hab)
  have hO0 : ((List.range (2 ^ n)).reverse.filter (fun p => p ≠ 0 ∧ p ≠ 2 ^ n / 2)).Pairwise
      (fun a b => b < a) :=
    (List.pairwise_reverse.2 List.pairwise_lt_range).filter _
  have hO : (((List.range (2 ^ n)).reverse.filter (fun p => p ≠ 0 ∧ p ≠ 2 ^ n / 2)).map
      (fun p => (3 : ℤ) ^ (2 * ((br n p + 2 ^ n - 2) % 2 ^ n) + 1))).Pairwise (Rel n) := by
    rw [List.pairwise_map]
    refine hO0.imp_of_mem (fun ha hb hab => ?_)
    simp only [List.mem_filter, List.mem_reverse, List.mem_range, decide_eq_true_eq] at ha hb
    exact rel_OO hn ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 hab
  unfold Wj
  rw [List.pairwise_append, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨⟨List.pairwise_singleton _ _, hE, ?_⟩, hO, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at ha; subst ha
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    exact rel_zero (pow3_ne_zero _)
  · intro a ha b hb
    obtain ⟨p', -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · simp only [List.mem_singleton] at ha; subst ha; exact rel_zero (pow3_ne_zero _)
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha; exact rel_EO hn _ _
  · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    exact rel_GT
  · intro a ha b hb
    have hb' : b = 2 * 3 ^ (2 * 2 ^ n - 3) ∨ b = 3 ^ (2 * 2 ^ n - 3) := by simpa using hb
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · simp only [List.mem_singleton] at ha; subst ha
        rcases hb' with rfl | rfl
        · exact rel_zero (by have := pow3_ne_zero (2 * 2 ^ n - 3); omega)
        · exact rel_zero (pow3_ne_zero _)
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
        rcases hb' with rfl | rfl
        · exact rel_EG hn _
        · rw [hT]; exact rel_EO hn _ _
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      simp only [List.mem_filter, List.mem_reverse, List.mem_range, decide_eq_true_eq] at hp
      obtain ⟨a1, a2⟩ := odd_idx hn hp.1 hp.2.1 hp.2.2
      have := br_lt' hp.1
      rw [a2]
      rcases hb' with rfl | rfl
      · exact rel_OG _ (by omega)
      · exact rel_OT hn (by omega)

end
end E195W

namespace E195W
open Erdos195 E195Tree

lemma val_odd {x : ℤ} (h : x % 2 = 1) : padicValInt 2 x = 0 :=
  padicValInt.eq_zero_of_not_dvd (by omega)

lemma val_mixed (s t : ℕ) : padicValInt 2 ((3 : ℤ) ^ (2 * t + 1) - 3 ^ (2 * s)) = 1 := by
  have h1 := pow3_mod8 (2 * t + 1); have h2 := pow3_mod8 (2 * s)
  rw [if_neg (by omega)] at h1; rw [if_pos (by omega)] at h2
  apply val_eq_of_cert <;> simp only [pow_one] <;> omega

lemma pow_split (e t : ℕ) : (3 : ℤ) ^ (2 * t + e) = 3 ^ e * 9 ^ t := by
  rw [pow_add, pow_mul]; norm_num; ring

lemma val_same (e s t : ℕ) (h : s ≠ t) :
    padicValInt 2 ((3 : ℤ) ^ (2 * t + e) - 3 ^ (2 * s + e)) = 3 + padicValInt 2 ((t : ℤ) - s) := by
  rw [pow_split, pow_split, ← mul_sub]
  have h9 : (9 : ℤ) ^ t - 9 ^ s ≠ 0 := by
    intro h0
    have : (9 : ℤ) ^ t = 9 ^ s := by linarith
    exact h (Int.pow_right_injective (by decide) this).symm
  rw [padicValInt.mul (pow3_ne_zero e) h9, val_odd (pow3_odd e), zero_add,
    nu2_nine_pow_sub t s (Ne.symm h)]

lemma cong9 {s q r : ℕ} (h : (2 : ℤ) ^ r ∣ (s : ℤ) - q) : (2 : ℤ) ^ (r + 3) ∣ (9 : ℤ) ^ s - 9 ^ q := by
  by_cases hsq : s = q
  · subst hsq; simp
  · have hd : (s : ℤ) - q ≠ 0 := by omega
    have h9 : (9 : ℤ) ^ s - 9 ^ q ≠ 0 := by
      intro h0
      exact hsq (Int.pow_right_injective (by decide) (by linarith : (9 : ℤ) ^ s = 9 ^ q))
    apply dvd_of_le_val
    rw [nu2_nine_pow_sub s q hsq]
    have := le_val_of_dvd hd h
    omega

/-- the bit forced at a same-parity power node, as a function of the node data `(e, r, q)` -/
def Fsig (e r q : ℕ) : Prop :=
  ((3 : ℤ) ^ e * 9 ^ q / 2 ^ (r + 3) + (if e = 0 then 1 else (((q + 2) / 2 ^ r : ℕ) : ℤ))) % 2 = 1

def Sig (k : ℕ) (a b : ℤ) : Prop :=
  (k = 0 ∧ ¬ bitOne b 0) ∨ (k = 1 ∧ bitOne b 1) ∨
  ∃ e < 2, ∃ r q : ℕ, q < 2 ^ r ∧ k = r + 3 ∧ a % 2 ^ k = (3 : ℤ) ^ e * 9 ^ q % 2 ^ k ∧
    (bitOne b k ↔ Fsig e r q)

lemma sig_same (e s t : ℕ) (he : e < 2) (hst : s ≠ t)
    (h0 : e = 0 → bitOne (t : ℤ) (padicValInt 2 ((t : ℤ) - s)))
    (h1 : e = 1 → ¬ bitOne ((t + 2 : ℕ) : ℤ) (padicValInt 2 ((t : ℤ) - s))) :
    Sig (padicValInt 2 ((3 : ℤ) ^ (2 * t + e) - 3 ^ (2 * s + e))) (3 ^ (2 * s + e)) (3 ^ (2 * t + e)) := by
  right; right
  rw [val_same e s t hst]
  set r := padicValInt 2 ((t : ℤ) - s)
  have hdv : (2 : ℤ) ^ r ∣ (t : ℤ) - s := two_pow_val_dvd _
  have hsq : (s : ℤ) % 2 ^ r = (t : ℤ) % 2 ^ r := emod_eq_of_dvd hdv
  have hsq' : s % 2 ^ r = t % 2 ^ r := by
    have c1 : ((s % 2 ^ r : ℕ) : ℤ) = (s : ℤ) % 2 ^ r := by push_cast; rfl
    have c2 : ((t % 2 ^ r : ℕ) : ℤ) = (t : ℤ) % 2 ^ r := by push_cast; rfl
    exact_mod_cast c1.trans (hsq.trans c2.symm)
  set q := t % 2 ^ r with hq
  have hqlt : q < 2 ^ r := Nat.mod_lt _ (by positivity)
  refine ⟨e, he, r, q, hqlt, by ring, ?_, ?_⟩
  · -- congruence of the first entry
    rw [pow_split, show 3 + r = r + 3 by ring]
    have hd : (2 : ℤ) ^ r ∣ (s : ℤ) - q := by
      have := Nat.div_add_mod s (2 ^ r)
      rw [hsq'] at this
      refine ⟨(s / 2 ^ r : ℕ), ?_⟩
      have : (s : ℤ) = 2 ^ r * ((s / 2 ^ r : ℕ) : ℤ) + (q : ℤ) := by exact_mod_cast this.symm
      linarith
    have := cong9 hd
    exact (emod_eq_of_dvd (by
      rw [show (3 : ℤ) ^ e * 9 ^ s - 3 ^ e * 9 ^ q = 3 ^ e * (9 ^ s - 9 ^ q) by ring]
      exact this.mul_left _)).symm
  · -- the bit
    unfold bitOne Fsig
    rw [pow_split, show 3 + r = r + 3 by ring, lift_bit _ (Odd.pow (by decide)) r t, ← hq]
    have ht := Nat.div_add_mod t (2 ^ r)
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · have b0 := h0 rfl
      rw [bitOne_nat] at b0
      simp only [if_true]
      have : (((t / 2 ^ r : ℕ) : ℤ)) % 2 = 1 := by exact_mod_cast b0
      omega
    · have b1 := h1 rfl
      rw [bitOne_nat] at b1
      simp only [show (1 : ℕ) ≠ 0 by omega, if_false]
      have e2 : (t + 2) / 2 ^ r = (q + 2) / 2 ^ r + t / 2 ^ r := by
        rw [← Nat.add_mul_div_left _ _ (show 0 < 2 ^ r by positivity)]
        congr 1; rw [hq]; omega
      rw [e2] at b1
      have : ((t / 2 ^ r : ℕ) : ℤ) % 2 = (((q + 2) / 2 ^ r : ℕ) : ℤ) % 2 := by
        have : t / 2 ^ r % 2 = (q + 2) / 2 ^ r % 2 := by omega
        exact_mod_cast this
      omega

lemma sig_consistent {k : ℕ} {a b a' b' : ℤ} (h : Sig k a b) (h' : Sig k a' b')
    (hc : a % 2 ^ k = a' % 2 ^ k) : (bitOne b k ↔ bitOne b' k) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨e, he, r, q, hq, rfl, ha, hb⟩ <;>
  rcases h' with ⟨hk', h'⟩ | ⟨hk', h'⟩ | ⟨e', he', r', q', hq', hk', ha', hb'⟩ <;>
  first | omega | (try simp only [] at *) <;> try tauto
  · -- both same-parity nodes
    have hr : r' = r := by omega
    subst hr
    rw [hb, hb']
    have hcong : (3 : ℤ) ^ e * 9 ^ q % 2 ^ (r' + 3) = 3 ^ e' * 9 ^ q' % 2 ^ (r' + 3) := by
      rw [← ha, ← ha']; exact hc
    have h8 : (3 : ℤ) ^ e * 9 ^ q % 8 = 3 ^ e' * 9 ^ q' % 8 := by
      have d8 : (8 : ℤ) ∣ 2 ^ (r' + 3) := ⟨2 ^ r', by ring⟩
      rw [← Int.emod_emod_of_dvd _ d8, hcong, Int.emod_emod_of_dvd _ d8]
    rw [← pow_split, ← pow_split, pow3_mod8, pow3_mod8] at h8
    have hee : e = e' := by
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;>
      rcases (by omega : e' = 0 ∨ e' = 1) with rfl | rfl <;> simp_all
    subst hee
    have hqq : q = q' := by
      by_contra hne
      have hdv : (2 : ℤ) ^ (r' + 3) ∣ 3 ^ e * 9 ^ q' - 3 ^ e * 9 ^ q :=
        Int.ModEq.dvd hcong
      rw [← pow_split, ← pow_split] at hdv
      have hne' : (3 : ℤ) ^ (2 * q' + e) - 3 ^ (2 * q + e) ≠ 0 := by
        intro h0; have := pow3_inj (by linarith : (3 : ℤ) ^ (2 * q' + e) = 3 ^ (2 * q + e)); omega
      have := le_val_of_dvd hne' hdv
      rw [val_same e q q' hne] at this
      have hd : (2 : ℤ) ^ r' ∣ (q' : ℤ) - q := dvd_of_le_val (by omega)
      have hlt : |(q' : ℤ) - q| < 2 ^ r' := by
        have : ((2 ^ r' : ℕ) : ℤ) = (2 : ℤ) ^ r' := by push_cast; rfl
        rw [abs_lt]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      omega
    subst hqq; rfl

end E195W

namespace E195W
open Erdos195 E195Tree

lemma pow3_ap_lt {u v w : ℕ} (huw : u < w) (e : 3 ^ u + 3 ^ w = 2 * 3 ^ v) : False := by
  rcases le_or_gt v u with hvu | huv
  · have h1 : 3 ^ v ≤ 3 ^ u := Nat.pow_le_pow_right (by norm_num) hvu
    have h2 : 3 ^ u < 3 ^ w := Nat.pow_lt_pow_right (by norm_num) huw
    omega
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt huw
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt huv
    have : 3 ^ u * (1 + 3 * 3 ^ a) = 3 ^ u * (2 * 3 * 3 ^ b) := by
      calc 3 ^ u * (1 + 3 * 3 ^ a) = 3 ^ u + 3 ^ (u + a + 1) := by ring
        _ = 2 * 3 ^ (u + b + 1) := e
        _ = 3 ^ u * (2 * 3 * 3 ^ b) := by ring
    have := Nat.eq_of_mul_eq_mul_left (by positivity) this
    omega

lemma pow3_ap {u v w : ℕ} (huv : u ≠ v) (e : (3 : ℤ) ^ u + 3 ^ w = 2 * 3 ^ v) : False := by
  have e' : 3 ^ u + 3 ^ w = 2 * 3 ^ v := by exact_mod_cast e
  rcases lt_trichotomy u w with h | rfl | h
  · exact pow3_ap_lt h e'
  · exact huv (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ u = 3 ^ v by omega))
  · exact pow3_ap_lt (v := v) h (by omega)

section
variable {n : ℕ}

/-- No in-order 3-term AP in `W_j`. -/
lemma Wj_no_inorder_ap (hn : 2 ≤ n) {a b : ℤ} (ha : a ∈ Wj n) (hb : b ∈ Wj n)
    (hc : 2 * b - a ∈ Wj n) (h1 : (Wj n).idxOf a < (Wj n).idxOf b)
    (h2 : (Wj n).idxOf b < (Wj n).idxOf (2 * b - a)) : False := by
  have hj := j_ge hn
  obtain ⟨hb0, haT, haG, -⟩ := rel_of_idx (Wj_pairwise hn) ha hb h1
  obtain ⟨hc0, hbT, hbG, -⟩ := rel_of_idx (Wj_pairwise hn) hb hc h2
  have hab := ne_of_idx h1
  rcases mem_Wj hn hb with rfl | rfl | ⟨v, hv, rfl⟩
  · exact hb0 rfl
  · have hc' := hbG rfl
    have : a = 3 ^ (2 * 2 ^ n - 3 + 1) := by rw [pow_succ]; linarith
    exact not_mem_pow hn (by omega) (this ▸ ha)
  · have hvm : v ≠ 2 * 2 ^ n - 3 := fun h => hbT (by rw [h])
    rcases mem_Wj hn ha with rfl | rfl | ⟨u, hu, rfl⟩
    · exact not_mem_two_pow hn hvm (by simpa using hc)
    · exact hvm (pow3_inj (haG rfl))
    · have huv : u ≠ v := fun h => hab (by rw [h])
      rcases mem_Wj hn hc with h | h | ⟨w, hw, h⟩
      · have := pow3_odd u; have := pow3_odd v; omega
      · have := pow3_odd u; have := pow3_odd v; have := pow3_odd (2 * 2 ^ n - 3); omega
      · exact pow3_ap huv (by linarith)

/-- Every open in-order pair has one of the three node signatures. -/
lemma sig_open (hn : 2 ≤ n) {a b : ℤ} (ha : a ∈ Wj n) (hb : b ∈ Wj n)
    (h : (Wj n).idxOf a < (Wj n).idxOf b) (n2 : 2 * b - a ∉ Wj n) (n3 : 3 * b - 2 * a ∉ Wj n) :
    Sig (padicValInt 2 (b - a)) a b := by
  have hj := j_ge hn
  obtain ⟨hb0, haT, haG, hord⟩ := rel_of_idx (Wj_pairwise hn) ha hb h
  have hab := ne_of_idx h
  rcases mem_Wj hn ha with rfl | rfl | ⟨u, hu, rfl⟩
  · rcases mem_Wj hn hb with rfl | rfl | ⟨v, hv, rfl⟩
    · exact absurd rfl hb0
    · right; left
      rw [sub_zero, show (2 : ℤ) * 3 ^ (2 * 2 ^ n - 3) = 2 ^ 1 * 3 ^ (2 * 2 ^ n - 3) by ring,
        val_two_pow_mul_odd 1 (Odd.pow (by decide))]
      refine ⟨rfl, ?_⟩
      unfold bitOne; have := pow3_odd (2 * 2 ^ n - 3); omega
    · exfalso
      rcases lt_or_eq_of_le hv with hv | rfl
      · exact n3 (by rw [mul_zero, sub_zero, ← pow_succ']; exact pow_mem hn (by omega))
      · exact n2 (by rw [sub_zero]; exact G_mem)
  · exfalso; have := haG rfl; subst this
    exact n2 (by rw [show (2 : ℤ) * 3 ^ (2 * 2 ^ n - 3) - 2 * 3 ^ (2 * 2 ^ n - 3) = 0 by ring]
                 exact zero_mem)
  · rcases mem_Wj hn hb with rfl | rfl | ⟨v, hv, rfl⟩
    · exact absurd rfl hb0
    · left
      rw [val_odd (by have := pow3_odd u; have := pow3_odd (2 * 2 ^ n - 3); omega)]
      refine ⟨rfl, ?_⟩
      unfold bitOne; simp only [pow_zero, Int.ediv_one]; omega
    · have huv : u ≠ v := fun h => hab (by rw [h])
      obtain ⟨o1, o2, o3⟩ := hord u v rfl rfl huv
      rcases Nat.even_or_odd' u with ⟨s, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' v with ⟨t, rfl | rfl⟩
      · have := sig_same 0 s t (by norm_num) (by omega)
          (fun _ => by have := o2 (by omega) (by omega); simpa [show 2 * t / 2 = t by omega,
            show 2 * s / 2 = s by omega] using this) (fun h => absurd h (by norm_num))
        simpa using this
      · right; left
        rw [val_mixed]; refine ⟨rfl, ?_⟩
        unfold bitOne; have := pow3_mod8 (2 * t + 1)
        rw [if_neg (by omega)] at this; simp only [pow_one]; omega
      · exact absurd (o1 (by omega)) (by omega)
      · have := sig_same 1 s t (by norm_num) (by omega) (fun h => absurd h (by norm_num))
          (fun _ => by have := o3 (by omega) (by omega); simpa [show (2 * t + 1) / 2 = t by omega,
            show (2 * s + 1) / 2 = s by omega] using this)
        exact this

end
end E195W

namespace Erdos195
open E195W E195Tree

/-- **Main theorem.** For every `n ≥ 2` the word `W_{2^n}` is tree-safe and a true root release. -/
theorem Wj_safe_released (n : ℕ) (hn : 2 ≤ n) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Wj n)) ∧
    ∀ a b : ℤ, a ∈ Wj n → b ∈ Wj n → (Wj n).idxOf a < (Wj n).idxOf b →
      2 * b - a ∉ Wj n → 3 * b - 2 * a ∉ Wj n → (b - a) % 2 = 1 → b % 2 = 0 := by
  refine ⟨(exists_treeLt_safe_iff _).2 ⟨fun a b ha hb hc i1 i2 =>
      absurd (Wj_no_inorder_ap hn ha hb hc i1 i2) id, ?_⟩, ?_⟩
  · intro a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk hr
    have s1 := sig_open hn ha hb i n2 n3
    have s2 := sig_open hn ha' hb' i' n2' n3'
    rw [← hk] at s2
    exact sig_consistent s1 s2 hr
  · intro a b ha hb i n2 n3 hodd
    have hk : padicValInt 2 (b - a) = 0 := val_odd hodd
    rcases sig_open hn ha hb i n2 n3 with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨e, -, r, q, -, h3, -⟩
    · unfold bitOne at h; simp only [pow_zero, Int.ediv_one] at h; omega
    · omega
    · omega

end Erdos195

#print axioms Erdos195.Wj_safe_released


open Erdos195 in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Wj n)) ∧
    ∀ a b : ℤ, a ∈ Wj n → b ∈ Wj n → (Wj n).idxOf a < (Wj n).idxOf b →
      2 * b - a ∉ Wj n → 3 * b - 2 * a ∉ Wj n → (b - a) % 2 = 1 → b % 2 = 0 := by
  first
  | exact Erdos195.Wj_safe_released
  | (apply Erdos195.Wj_safe_released <;> assumption)

#print axioms solution
