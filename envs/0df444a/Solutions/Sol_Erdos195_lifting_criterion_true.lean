-- Prove2me | solution 1 for Erdos195.lifting_criterion_true
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T15:11:23.178832+00:00
-- url     : https://prove2.me/submissions/62b1351a-879d-4cd2-9c16-a6c05565262d

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


namespace Erdos195
open E195Tree E195Par

/-- **Symmetric lifting lemma.** Let `S` be safe for a tree witness `θ` with `θ 0 0 = false`
(equivalently: `S` is SAFE and RELEASED — every open odd-difference pair ends at an even entry).
Append a block `R` of even entries and then a new odd entry `y`. If the halved even part of `S ++ R`
is safe for the shifted witness `θ(k+1, 2r)`, the halved odd part of `S ++ [y]` is safe for
`θ(k+1, 2r+1)`, and the even entries of `S ++ R` are closed under reflection `a ↦ 2y - a`, then
`S ++ R ++ [y]` is safe for the same `θ` (hence again SAFE and RELEASED). -/
theorem symmetric_lifting (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = false) (S R : List ℤ) (y : ℤ)
    (hS : Safe (treeLt θ) S) (hRe : ∀ r ∈ R, r % 2 = 0) (hy : y % 2 = 1) (hyS : y ∉ S)
    (hE : Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
      (((S ++ R).filter (fun x => decide (x % 2 = 0))).map (· / 2)))
    (hO : Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
      (((S ++ [y]).filter (fun x => decide (x % 2 = 1))).map (· / 2)))
    (hsym : ∀ a ∈ S ++ R, a % 2 = 0 → 2 * y - a ∈ S ++ R) :
    Safe (treeLt θ) (S ++ R ++ [y]) := by
  obtain ⟨-, -, hMS⟩ := (safe_parity_decomp θ S).1 hS
  set P := S ++ R with hP
  set Q := P ++ [y] with hQ
  have hyP : y ∉ P := by
    intro h; rcases List.mem_append.1 h with h | h
    · exact hyS h
    · have := hRe y h; omega
  have memQ : ∀ x, x ∈ Q ↔ x ∈ P ∨ x = y := by intro x; simp [Q]
  have memP : ∀ x, x ∈ P ↔ x ∈ S ∨ x ∈ R := by intro x; simp [P]
  have idxQP : ∀ x ∈ P, Q.idxOf x = P.idxOf x := fun x hx => List.idxOf_append_of_mem hx
  have idxPS : ∀ x ∈ S, P.idxOf x = S.idxOf x := fun x hx => List.idxOf_append_of_mem hx
  have idxQS : ∀ x ∈ S, Q.idxOf x = S.idxOf x := fun x hx =>
    (idxQP x ((memP x).2 (Or.inl hx))).trans (idxPS x hx)
  have idxy : Q.idxOf y = P.length := by
    rw [List.idxOf_append_of_notMem hyP]; simp
  have ltP : ∀ x ∈ P, Q.idxOf x < Q.idxOf y := by
    intro x hx; rw [idxQP x hx, idxy]; exact List.idxOf_lt_length_of_mem hx
  have ltS : ∀ x ∈ S, Q.idxOf x < S.length := by
    intro x hx; rw [idxQS x hx]; exact List.idxOf_lt_length_of_mem hx
  have geS : ∀ x, x ∉ S → S.length ≤ Q.idxOf x := by
    intro x hx
    rw [hQ, hP, List.append_assoc, List.idxOf_append_of_notMem hx]; omega
  -- prefix property
  have pre : ∀ a b, b ∈ S → Q.idxOf a < Q.idxOf b → a ∈ S := by
    intro a b hb i
    by_contra ha
    have := geS a ha; have := ltS b hb; omega
  -- odd elements of Q outside S are y
  have oddQ : ∀ x ∈ Q, x % 2 = 1 → x ∈ S ∨ x = y := by
    intro x hx hxo
    rcases (memQ x).1 hx with h | h
    · rcases (memP x).1 h with h | h
      · exact Or.inl h
      · have := hRe x h; omega
    · exact Or.inr h
  have notS_of_notQ : ∀ x, x ∉ Q → x ∉ S := fun x hx h =>
    hx ((memQ x).2 (Or.inl ((memP x).2 (Or.inl h))))
  have SQ : ∀ x ∈ S, x ∈ Q := fun x hx => (memQ x).2 (Or.inl ((memP x).2 (Or.inl hx)))
  -- even/odd filters
  have hEQ : Q.filter (fun x => decide (x % 2 = 0)) = P.filter (fun x => decide (x % 2 = 0)) := by
    rw [hQ, List.filter_append]
    have : [y].filter (fun x => decide (x % 2 = 0)) = [] := by
      simp only [List.filter_cons, List.filter_nil]; simp [hy]
    rw [this, List.append_nil]
  have hOQ : Q.filter (fun x => decide (x % 2 = 1)) = (S ++ [y]).filter (fun x => decide (x % 2 = 1)) := by
    rw [hQ, hP, List.filter_append, List.filter_append, List.filter_append]
    have : R.filter (fun x => decide (x % 2 = 1)) = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx; have := hRe x hx; simp; omega
    rw [this, List.append_nil]
  refine (safe_parity_decomp θ Q).2 ⟨by rw [hEQ]; exact hE, by rw [hOQ]; exact hO, ?_⟩
  intro a b ha hb hab i
  refine ⟨fun hc ic => ?_, fun nc nd => ?_⟩
  · -- in-order 3-AP a, b, c = 2b - a
    by_cases hcS : 2 * b - a ∈ S
    · have hbS := pre b _ hcS ic
      have haS := pre a b hbS i
      have := (hMS a b haS hbS hab (by rw [← idxQS a haS, ← idxQS b hbS]; exact i)).1 hcS
        (by rw [← idxQS b hbS, ← idxQS _ hcS]; exact ic)
      refine ⟨SQ _ this.1, ?_⟩
      rw [idxQS _ this.1, idxQS _ hcS]; exact this.2
    · rcases Int.emod_two_eq_zero_or_one a with hae | hao
      · -- a even, b odd: b ∈ S
        have hbo : b % 2 = 1 := by omega
        have hbS : b ∈ S := by
          rcases oddQ b hb hbo with h | h
          · exact h
          · exfalso
            have hcP : 2 * b - a ∈ P := by
              rcases (memQ _).1 hc with h' | h'
              · exact h'
              · omega
            have h1 := ltP _ hcP
            have h2 : Q.idxOf b = Q.idxOf y := by rw [h]
            omega
        have haS := pre a b hbS i
        have hdS : 3 * b - 2 * a ∈ S := by
          by_contra hdS
          have := (hMS a b haS hbS hab (by rw [← idxQS a haS, ← idxQS b hbS]; exact i)).2 hcS hdS
          rw [h00] at this; simp at this; omega
        exact ⟨SQ _ hdS, by have := ltS _ hdS; have := geS _ hcS; omega⟩
      · -- a odd: c odd, so c = y
        have hcy : 2 * b - a = y := by
          rcases oddQ _ hc (by omega) with h | h
          · exact absurd h hcS
          · exact h
        have hbe : b % 2 = 0 := by omega
        have hbP : b ∈ P := by
          rcases (memQ b).1 hb with h | h
          · exact h
          · omega
        have hd : 3 * b - 2 * a = 2 * y - b := by rw [← hcy]; ring
        have hdP := hsym b hbP hbe
        rw [hd, hcy]
        exact ⟨(memQ _).2 (Or.inl hdP), ltP _ hdP⟩
  · -- open odd-difference pair: b must be even
    rw [h00]
    simp only [Bool.false_eq_true, false_iff]
    intro hbo
    rcases oddQ b hb hbo with hbS | hby
    · have haS := pre a b hbS i
      have := (hMS a b haS hbS hab (by rw [← idxQS a haS, ← idxQS b hbS]; exact i)).2
        (notS_of_notQ _ nc) (notS_of_notQ _ nd)
      rw [h00] at this; simp at this; omega
    · have haP : a ∈ P := by
        rcases (memQ a).1 ha with h | h
        · exact h
        · subst h; subst hby; exact absurd i (lt_irrefl _)
      have hae : a % 2 = 0 := by omega
      apply nc; rw [hby]; exact (memQ _).2 (Or.inl (hsym a haP hae))

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

namespace Erdos195
open E195W E195Tree

/-- **Extremal-parity lemma.** -/
theorem extremal_parity (A : List ℤ) (a b : ℤ) (rest : List ℤ) (hA : A = a :: b :: rest)
    (hii : ∀ x y x' y' : ℤ, x ∈ A → y ∈ A → A.idxOf x < A.idxOf y →
      2 * y - x ∉ A → 3 * y - 2 * x ∉ A →
      x' ∈ A → y' ∈ A → A.idxOf x' < A.idxOf y' →
      2 * y' - x' ∉ A → 3 * y' - 2 * x' ∉ A →
      padicValInt 2 (y - x) = padicValInt 2 (y' - x') →
      x % 2 ^ padicValInt 2 (y - x) = x' % 2 ^ padicValInt 2 (y - x) →
      (bitOne y (padicValInt 2 (y - x)) ↔ bitOne y' (padicValInt 2 (y - x))))
    (hab : (b - a) % 2 = 1) (L U : ℤ) (hL : L ∈ A) (hU : U ∈ A)
    (hbd : ∀ x ∈ A, L ≤ x ∧ x ≤ U) (hLa : L < a) (haU : a < U) :
    (U - L) % 2 = 0 := by
  by_contra hpar
  have hba : b ≠ a := by rintro rfl; simp at hab
  have haA : a ∈ A := by simp [hA]
  have hbA : b ∈ A := by simp [hA]
  have i0 : A.idxOf a = 0 := by simp [hA]
  have i1 : A.idxOf b = 1 := by
    rw [hA, List.idxOf_cons_ne _ (Ne.symm hba)]; simp
  have ige1 : ∀ x, x ≠ a → 1 ≤ A.idxOf x := by
    intro x hxa; rw [hA, List.idxOf_cons_ne _ (Ne.symm hxa)]; omega
  have ige2 : ∀ x, x ≠ a → x ≠ b → 2 ≤ A.idxOf x := by
    intro x hxa hxb
    rw [hA, List.idxOf_cons_ne _ (Ne.symm hxa), List.idxOf_cons_ne _ (Ne.symm hxb)]; omega
  have openU : ∀ p ∈ A, p ≠ U → 2 * U - p ∉ A ∧ 3 * U - 2 * p ∉ A := by
    intro p hp hne
    have := hbd p hp
    constructor <;> intro h <;> have := hbd _ h <;> omega
  have openL : ∀ p ∈ A, p ≠ L → 2 * L - p ∉ A ∧ 3 * L - 2 * p ∉ A := by
    intro p hp hne
    have := hbd p hp
    constructor <;> intro h <;> have := hbd _ h <;> omega
  have v0 : ∀ d : ℤ, d % 2 = 1 → padicValInt 2 d = 0 := fun d hd =>
    val_eq_of_cert (by simp) (by simpa using hd)
  have hbb := hbd b hbA
  by_cases hUa : (U - a) % 2 = 1
  · -- z = U, w = L
    have h1 : (U - a) % 2 = 1 := hUa
    have h2 : (L - b) % 2 = 1 := by omega
    have hLb : L ≠ b := by intro h; subst h; omega
    have := hii a U b L haA hU (by rw [i0]; exact ige1 U (by omega))
      (openU a haA (by omega)).1 (openU a haA (by omega)).2 hbA hL
      (by rw [i1]; exact ige2 L (by omega) hLb)
      (openL b hbA (Ne.symm hLb)).1 (openL b hbA (Ne.symm hLb)).2
      (by rw [v0 _ h1, v0 _ h2]) (by rw [v0 _ h1]; simp)
    rw [v0 _ h1] at this
    simp [bitOne] at this
    omega
  · -- z = L, w = U
    have h1 : (L - a) % 2 = 1 := by omega
    have h2 : (U - b) % 2 = 1 := by omega
    have hUb : U ≠ b := by intro h; subst h; omega
    have := hii a L b U haA hL (by rw [i0]; exact ige1 L (by omega))
      (openL a haA (by omega)).1 (openL a haA (by omega)).2 hbA hU
      (by rw [i1]; exact ige2 U (by omega) hUb)
      (openU b hbA (Ne.symm hUb)).1 (openU b hbA (Ne.symm hUb)).2
      (by rw [v0 _ h1, v0 _ h2]) (by rw [v0 _ h1]; simp)
    rw [v0 _ h1] at this
    simp [bitOne] at this
    omega

/-- **No symmetric completion of (0,-1) about 1/2.** -/
theorem no_symmetric_completion (A rest : List ℤ) (hA : A = 0 :: -1 :: rest)
    (hii : ∀ x y x' y' : ℤ, x ∈ A → y ∈ A → A.idxOf x < A.idxOf y →
      2 * y - x ∉ A → 3 * y - 2 * x ∉ A →
      x' ∈ A → y' ∈ A → A.idxOf x' < A.idxOf y' →
      2 * y' - x' ∉ A → 3 * y' - 2 * x' ∉ A →
      padicValInt 2 (y - x) = padicValInt 2 (y' - x') →
      x % 2 ^ padicValInt 2 (y - x) = x' % 2 ^ padicValInt 2 (y - x) →
      (bitOne y (padicValInt 2 (y - x)) ↔ bitOne y' (padicValInt 2 (y - x))))
    (hsym : ∀ u ∈ A, 1 - u ∈ A) : False := by
  have hne : A.toFinset.Nonempty := ⟨0, by simp [hA]⟩
  set L := A.toFinset.min' hne with hLdef
  set U := A.toFinset.max' hne with hUdef
  have hL : L ∈ A := List.mem_toFinset.1 (Finset.min'_mem _ _)
  have hU : U ∈ A := List.mem_toFinset.1 (Finset.max'_mem _ _)
  have hbd : ∀ x ∈ A, L ≤ x ∧ x ≤ U := fun x hx =>
    ⟨Finset.min'_le _ _ (List.mem_toFinset.2 hx), Finset.le_max' _ _ (List.mem_toFinset.2 hx)⟩
  have hm1 : (-1 : ℤ) ∈ A := by simp [hA]
  have h2 : (2 : ℤ) ∈ A := by simpa using hsym _ hm1
  have b1 := hbd _ hm1
  have b2 := hbd _ h2
  have b3 := hbd _ (hsym _ hL)
  have b4 := hbd _ (hsym _ hU)
  have := extremal_parity A 0 (-1) rest hA hii (by norm_num) L U hL hU hbd (by omega) (by omega)
  omega

/-- **Reflection-only obstruction** for `S = (0,-2)` and target `y = 1`. -/
theorem reflection_only_obstruction :
    ¬ ∃ R : List ℤ, (∀ r ∈ R, r % 2 = 0) ∧
      (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([0, -2] ++ R ++ [1])) ∧
      ∀ a b : ℤ, a ∈ [0, -2] ++ R ++ [1] → b ∈ [0, -2] ++ R ++ [1] →
        ([0, -2] ++ R ++ [1]).idxOf a < ([0, -2] ++ R ++ [1]).idxOf b →
        2 * b - a ∉ [0, -2] ++ R ++ [1] → 3 * b - 2 * a ∉ [0, -2] ++ R ++ [1] →
        (b - a) % 2 = 1 → b % 2 = 0 := by
  rintro ⟨R, hR, hS, hrel⟩
  set P : List ℤ := [0, -2] ++ R with hP
  set Q : List ℤ := P ++ [1] with hQ
  obtain ⟨-, hii⟩ := (exists_treeLt_safe_iff Q).1 hS
  have memQ : ∀ x, x ∈ Q ↔ x ∈ P ∨ x = 1 := by intro x; simp [Q]
  have Pev : ∀ x ∈ P, x % 2 = 0 := by
    intro x hx
    simp only [P, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with h | h | h
    · subst h; rfl
    · subst h; rfl
    · exact hR x h
  have h1P : (1 : ℤ) ∉ P := fun h => by have := Pev 1 h; omega
  have idxP : ∀ x ∈ P, Q.idxOf x = P.idxOf x := fun x hx => List.idxOf_append_of_mem hx
  have idx1 : Q.idxOf 1 = P.length := by
    rw [List.idxOf_append_of_notMem h1P]; simp
  have before1 : ∀ x ∈ P, Q.idxOf x < Q.idxOf 1 := by
    intro x hx; rw [idxP x hx, idx1]; exact List.idxOf_lt_length_of_mem hx
  have refl : ∀ x ∈ P, 2 - x ∈ P := by
    intro x hx
    have hxe := Pev x hx
    by_contra hn
    have n2 : 2 * 1 - x ∉ Q := by
      rw [memQ]; rintro (h | h)
      · exact hn (by simpa using h)
      · omega
    have n3 : 3 * 1 - 2 * x ∉ Q := by
      rw [memQ]; rintro (h | h)
      · have := Pev _ h; omega
      · omega
    have := hrel x 1 ((memQ x).2 (Or.inl hx)) ((memQ 1).2 (Or.inr rfl)) (before1 x hx) n2 n3
      (by omega)
    omega
  have hQc : Q = 0 :: -2 :: (R ++ [1]) := by simp [Q, P]
  have i0 : Q.idxOf 0 = 0 := by rw [hQc]; simp
  have i1 : Q.idxOf (-2) = 1 := by rw [hQc, List.idxOf_cons_ne _ (by norm_num)]; simp
  have ige1 : ∀ x : ℤ, x ≠ 0 → 1 ≤ Q.idxOf x := by
    intro x hx; rw [hQc, List.idxOf_cons_ne _ (Ne.symm hx)]; omega
  have ige2 : ∀ x : ℤ, x ≠ 0 → x ≠ -2 → 2 ≤ Q.idxOf x := by
    intro x hx hx2
    rw [hQc, List.idxOf_cons_ne _ (Ne.symm hx), List.idxOf_cons_ne _ (Ne.symm hx2)]; omega
  have hne : P.toFinset.Nonempty := ⟨0, by simp [P]⟩
  set Le := P.toFinset.min' hne with hLdef
  set Ue := P.toFinset.max' hne with hUdef
  have hLe : Le ∈ P := List.mem_toFinset.1 (Finset.min'_mem _ _)
  have hUe : Ue ∈ P := List.mem_toFinset.1 (Finset.max'_mem _ _)
  have hbd : ∀ x ∈ P, Le ≤ x ∧ x ≤ Ue := fun x hx =>
    ⟨Finset.min'_le _ _ (List.mem_toFinset.2 hx), Finset.le_max' _ _ (List.mem_toFinset.2 hx)⟩
  have hm2 : (-2 : ℤ) ∈ P := by simp [P]
  have h0 : (0 : ℤ) ∈ P := by simp [P]
  have h4 : (4 : ℤ) ∈ P := by simpa using refl _ hm2
  have b1 := hbd _ hm2
  have b2 := hbd _ h4
  have b3 := hbd _ (refl _ hLe)
  have b4 := hbd _ (refl _ hUe)
  have eL := Pev _ hLe
  have eU := Pev _ hUe
  have notQ : ∀ y : ℤ, (y < Le ∨ Ue < y) → y ≠ 1 → y ∉ Q := by
    intro y hy hy1; rw [memQ]; rintro (h | h)
    · have := hbd y h; omega
    · exact hy1 h
  have memQP : ∀ x ∈ P, x ∈ Q := fun x hx => (memQ x).2 (Or.inl hx)
  by_cases hU4 : Ue % 4 = 2
  · -- z = Ue, w = Le
    have c1 : padicValInt 2 (Ue - 0) = 1 := val_eq_of_cert (by norm_num; omega) (by norm_num; omega)
    have c2 : padicValInt 2 (Le - -2) = 1 := val_eq_of_cert (by norm_num; omega) (by norm_num; omega)
    have := hii 0 Ue (-2) Le (memQP _ h0) (memQP _ hUe) (by rw [i0]; exact ige1 _ (by omega))
      (notQ _ (by omega) (by omega)) (notQ _ (by omega) (by omega))
      (memQP _ hm2) (memQP _ hLe) (by rw [i1]; exact ige2 _ (by omega) (by omega))
      (notQ _ (by omega) (by omega)) (notQ _ (by omega) (by omega))
      (by rw [c1, c2]) (by rw [c1]; norm_num)
    rw [c1] at this
    simp only [bitOne, pow_one] at this
    omega
  · -- z = Le, w = Ue
    have c1 : padicValInt 2 (Le - 0) = 1 := val_eq_of_cert (by norm_num; omega) (by norm_num; omega)
    have c2 : padicValInt 2 (Ue - -2) = 1 := val_eq_of_cert (by norm_num; omega) (by norm_num; omega)
    have := hii 0 Le (-2) Ue (memQP _ h0) (memQP _ hLe) (by rw [i0]; exact ige1 _ (by omega))
      (notQ _ (by omega) (by omega)) (notQ _ (by omega) (by omega))
      (memQP _ hm2) (memQP _ hUe) (by rw [i1]; exact ige2 _ (by omega) (by omega))
      (notQ _ (by omega) (by omega)) (notQ _ (by omega) (by omega))
      (by rw [c1, c2]) (by rw [c1]; norm_num)
    rw [c1] at this
    simp only [bitOne, pow_one] at this
    omega

end Erdos195


namespace E195S65
open Erdos195 E195Tree E195Par

/-- index facts for words `(0 :: 1 :: -1 :: rest) ++ [2]` -/
lemma idx_facts (A rest : List ℤ) (hA : A = (0 :: 1 :: -1 :: rest) ++ [2]) (h2 : (2 : ℤ) ∉ rest) :
    A.idxOf 0 = 0 ∧ A.idxOf 1 = 1 ∧
    (∀ x : ℤ, x ≠ 0 → 1 ≤ A.idxOf x) ∧
    (∀ x : ℤ, x ≠ 0 → x ≠ 1 → 2 ≤ A.idxOf x) ∧
    (∀ x : ℤ, x ≠ 0 → x ≠ 1 → x ≠ -1 → 3 ≤ A.idxOf x) ∧
    (∀ x : ℤ, x ∈ A → x ≠ 2 → A.idxOf x < A.idxOf 2) := by
  have hc : A = 0 :: 1 :: -1 :: (rest ++ [2]) := by rw [hA]; rfl
  refine ⟨by rw [hc]; simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, List.idxOf_cons_ne _ (by norm_num)]; simp
  · intro x h0; rw [hc, List.idxOf_cons_ne _ (Ne.symm h0)]; omega
  · intro x h0 h1
    rw [hc, List.idxOf_cons_ne _ (Ne.symm h0), List.idxOf_cons_ne _ (Ne.symm h1)]; omega
  · intro x h0 h1 h3
    rw [hc, List.idxOf_cons_ne _ (Ne.symm h0), List.idxOf_cons_ne _ (Ne.symm h1),
      List.idxOf_cons_ne _ (Ne.symm h3)]; omega
  · intro x hx hx2
    have hxP : x ∈ (0 :: 1 :: -1 :: rest) := by
      rw [hA, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hx
      · simp at hx; exact absurd hx hx2
    have h2P : (2 : ℤ) ∉ (0 :: 1 :: -1 :: rest) := by
      simp only [List.mem_cons, not_or]; exact ⟨by norm_num, by norm_num, by norm_num, h2⟩
    rw [hA, List.idxOf_append_of_mem hxP, List.idxOf_append_of_notMem h2P]
    have := List.idxOf_lt_length_of_mem hxP
    omega

end E195S65

namespace Erdos195
open E195Tree E195Par E195S65

/-- **Target-last forces release.** If a word starting `0, 1, -1` and ending at `2` (with `2` not
occurring earlier) is safe for a tree witness `θ`, then `θ 0 0 = false` and the word is RELEASED:
every in-order OPEN pair with odd difference ends at an even entry. -/
theorem target_last_released (θ : ℕ → ℤ → Bool) (A rest : List ℤ)
    (hA : A = (0 :: 1 :: -1 :: rest) ++ [2]) (h2 : (2 : ℤ) ∉ rest)
    (hS : Safe (treeLt θ) A) :
    θ 0 0 = false ∧
    ∀ a b : ℤ, a ∈ A → b ∈ A → A.idxOf a < A.idxOf b → (b - a) % 2 = 1 →
      2 * b - a ∉ A → 3 * b - 2 * a ∉ A → b % 2 = 0 := by
  obtain ⟨i0, i1, ige1, ige2, -, ilt2⟩ := idx_facts A rest hA h2
  obtain ⟨hE, hO, hM⟩ := (safe_parity_decomp θ A).1 hS
  have hAPC := ((treeLt_safe_iff θ A).1 hS).1
  have root : ∀ a b : ℤ, a ∈ A → b ∈ A → A.idxOf a < A.idxOf b → (b - a) % 2 = 1 →
      2 * b - a ∉ A → 3 * b - 2 * a ∉ A → (θ 0 0 = true ↔ b % 2 = 1) :=
    fun a b ha hb i hab n2 n3 => (hM a b ha hb hab i).2 n2 n3
  have m0 : (0 : ℤ) ∈ A := by simp [hA]
  have m1 : (1 : ℤ) ∈ A := by simp [hA]
  have mm1 : (-1 : ℤ) ∈ A := by simp [hA]
  have m2 : (2 : ℤ) ∈ A := by simp [hA]
  have m3 : (3 : ℤ) ∈ A := by
    have := hAPC 0 1 m0 m1 (by simpa using m2) (by omega)
      (by have := ilt2 1 m1 (by norm_num); simpa using this)
    simpa using this.1
  have hne : (A.toFinset).Nonempty := ⟨0, by simp [m0]⟩
  set L := A.toFinset.min' hne with hLdef
  set U := A.toFinset.max' hne with hUdef
  have hL : L ∈ A := List.mem_toFinset.1 (Finset.min'_mem _ hne)
  have hU : U ∈ A := List.mem_toFinset.1 (Finset.max'_mem _ hne)
  have hbd : ∀ x ∈ A, L ≤ x ∧ x ≤ U := fun x hx =>
    ⟨Finset.min'_le _ x (List.mem_toFinset.2 hx), Finset.le_max' _ x (List.mem_toFinset.2 hx)⟩
  have hLm1 : L ≤ -1 := (hbd _ mm1).1
  have hU3 : 3 ≤ U := (hbd _ m3).2
  have h00 : θ 0 0 = false := by
    rcases Int.emod_two_eq_zero_or_one L with hLe | hLo
    · -- L even: the open pair (1, L) ends even
      have := root 1 L m1 hL (by rw [i1]; exact ige2 L (by omega) (by omega)) (by omega)
        (fun h => by have := (hbd _ h).1; omega) (fun h => by have := (hbd _ h).1; omega)
      cases h : θ 0 0
      · rfl
      · rw [h] at this; have := this.1 rfl; omega
    · exfalso
      have hii := ((exists_treeLt_safe_iff A).1 ⟨θ, hS⟩).2
      have hpar := extremal_parity A 0 1 (-1 :: rest ++ [2]) (by rw [hA]; rfl) hii (by norm_num)
        L U hL hU hbd (by omega) (by omega)
      have hUo : U % 2 = 1 := by omega
      -- the open pair (0, U) forces root bit 1
      have hT : θ 0 0 = true := by
        have := root 0 U m0 hU (by rw [i0]; exact ige1 U (by omega)) (by omega)
          (fun h => by have := (hbd _ h).2; omega) (fun h => by have := (hbd _ h).2; omega)
        exact this.2 hUo
      rcases lt_trichotomy (2 - L) (U - 2) with hlt | heq | hgt
      · have := root U 2 hU m2 (ilt2 U hU (by omega)) (by omega)
          (fun h => by have := (hbd _ h).1; omega) (fun h => by have := (hbd _ h).1; omega)
        rw [hT] at this; have := this.1 rfl; omega
      · -- L + U = 4: contradiction in the odd half
        have hO' := ((exists_treeLt_safe_iff _).1 ⟨_, hO⟩).2
        set B := (A.filter (fun x => decide (x % 2 = 1))).map (· / 2) with hB
        have hBc : B = 0 :: -1 :: (((rest ++ [2]).filter (fun x => decide (x % 2 = 1))).map (· / 2)) := by
          rw [hB, hA]; simp
        have memB : ∀ z ∈ A, z % 2 = 1 → z / 2 ∈ B := by
          intro z hz hzo
          rw [hB]; exact List.mem_map.2 ⟨z, List.mem_filter.2 ⟨hz, by simpa using hzo⟩, rfl⟩
        have bdB : ∀ x ∈ B, L / 2 ≤ x ∧ x ≤ U / 2 := by
          intro x hx
          rw [hB] at hx
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
          have := hbd z (List.mem_filter.1 hz).1
          omega
        have := extremal_parity B 0 (-1) _ hBc hO' (by norm_num) (L / 2) (U / 2)
          (memB L hL hLo) (memB U hU hUo) bdB (by omega) (by omega)
        omega
      · have := root L 2 hL m2 (ilt2 L hL (by omega)) (by omega)
          (fun h => by have := (hbd _ h).2; omega) (fun h => by have := (hbd _ h).2; omega)
        rw [hT] at this; have := this.1 rfl; omega
  refine ⟨h00, fun a b ha hb i hab n2 n3 => ?_⟩
  have := root a b ha hb i hab n2 n3
  rw [h00] at this
  rcases Int.emod_two_eq_zero_or_one b with h | h
  · exact h
  · exact absurd (this.2 h) (by simp)

/-- **Odd-only auxiliaries cannot put `2` last after `0, 1, -1`.** There is no tree-safe word
`0, 1, -1, R, 2` in which every entry of `R` is odd. -/
theorem no_odd_target_last (R : List ℤ) (hR : ∀ r ∈ R, r % 2 = 1) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ((0 :: 1 :: -1 :: R) ++ [2]) := by
  rintro ⟨θ, hS⟩
  set A := (0 :: 1 :: -1 :: R) ++ [2] with hA
  have h2 : (2 : ℤ) ∉ R := fun h => by have := hR 2 h; norm_num at this
  obtain ⟨-, hrel⟩ := target_last_released θ A R hA h2 hS
  obtain ⟨i0, i1, ige1, -, -, ilt2⟩ := idx_facts A R hA h2
  have hAPC := ((treeLt_safe_iff θ A).1 hS).1
  have m0 : (0 : ℤ) ∈ A := by simp [hA]
  have m1 : (1 : ℤ) ∈ A := by simp [hA]
  have m2 : (2 : ℤ) ∈ A := by simp [hA]
  have m3 : (3 : ℤ) ∈ A := by
    have := hAPC 0 1 m0 m1 (by simpa using m2) (by omega)
      (by have := ilt2 1 m1 (by norm_num); simpa using this)
    simpa using this.1
  -- the only even entries are 0 and 2
  have hev : ∀ x ∈ A, x % 2 = 0 → x = 0 ∨ x = 2 := by
    intro x hx hxe
    rw [hA] at hx
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil] at hx
    rcases hx with ((h | h | h | h) | h | h)
    · exact Or.inl h
    · subst h; norm_num at hxe
    · subst h; norm_num at hxe
    · have := hR x h; omega
    · exact Or.inr h
    · exact h.elim
  have podd : ∀ m : ℕ, (3 : ℤ) ^ m % 2 = 1 := by
    intro m; exact Int.odd_iff.1 (Odd.pow (by decide))
  have chain : ∀ m : ℕ, 1 ≤ m → (3 : ℤ) ^ m ∈ A := by
    intro m hm
    induction m with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simpa using m3
      · have hin := ih hn
        have hpos : (3 : ℤ) ≤ 3 ^ n := by
          calc (3 : ℤ) = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
        by_contra hc
        have := hrel 0 (3 ^ n) m0 hin (by rw [i0]; exact ige1 _ (by omega))
          (by have := podd n; omega)
          (fun h => by
            rcases hev _ h (by omega) with h' | h' <;> omega)
          (fun h => hc (by rw [pow_succ]; simpa [mul_comm] using h))
        have := podd n; omega
  -- a finite list cannot contain all powers of 3
  have hne : (A.toFinset).Nonempty := ⟨0, by simp [m0]⟩
  set U := A.toFinset.max' hne
  have hbd : ∀ x ∈ A, x ≤ U := fun x hx => Finset.le_max' _ x (List.mem_toFinset.2 hx)
  have hU0 : 0 ≤ U := hbd 0 m0
  have hlt : U < (3 : ℤ) ^ (U.toNat + 1) := by
    have h := Nat.lt_pow_self (n := U.toNat + 1) (a := 3) (by norm_num)
    have h' : ((U.toNat + 1 : ℕ) : ℤ) < ((3 ^ (U.toNat + 1) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    omega
  have := hbd _ (chain (U.toNat + 1) (by omega))
  omega

end Erdos195


namespace Erdos195
open E195Tree E195Par E195S65

/-- **Compulsory witnesses for target-last absorption of `2` into `0, 1, -1`.** If the word
`0, 1, -1, rest, 2` (with `2 ∉ rest`) is safe for some tree witness, then it contains `-3` and `-5`,
and each of the two rays `3^m` and `-3^m` is capped: for some `m ≥ 1` (resp. `n ≥ 1`) the entry
`3^m` (resp. `-3^n`) is present, the next power is absent, and its double is present and placed
before it. -/
theorem target_last_caps (θ : ℕ → ℤ → Bool) (A rest : List ℤ)
    (hA : A = (0 :: 1 :: -1 :: rest) ++ [2]) (h2 : (2 : ℤ) ∉ rest)
    (hS : Safe (treeLt θ) A) :
    (-3 : ℤ) ∈ A ∧ (-5 : ℤ) ∈ A ∧
    (∃ m : ℕ, 1 ≤ m ∧ (3 : ℤ) ^ m ∈ A ∧ (3 : ℤ) ^ (m + 1) ∉ A ∧ 2 * (3 : ℤ) ^ m ∈ A ∧
      A.idxOf (2 * (3 : ℤ) ^ m) < A.idxOf ((3 : ℤ) ^ m)) ∧
    (∃ n : ℕ, 1 ≤ n ∧ -(3 : ℤ) ^ n ∈ A ∧ -(3 : ℤ) ^ (n + 1) ∉ A ∧ -2 * (3 : ℤ) ^ n ∈ A ∧
      A.idxOf (-2 * (3 : ℤ) ^ n) < A.idxOf (-(3 : ℤ) ^ n)) := by
  obtain ⟨-, hrel⟩ := target_last_released θ A rest hA h2 hS
  obtain ⟨i0, i1, ige1, ige2, ige3, ilt2⟩ := idx_facts A rest hA h2
  have hAPC := ((treeLt_safe_iff θ A).1 hS).1
  have hc : A = 0 :: 1 :: -1 :: (rest ++ [2]) := by rw [hA]; rfl
  have im1 : A.idxOf (-1) = 2 := by
    rw [hc, List.idxOf_cons_ne _ (by norm_num), List.idxOf_cons_ne _ (by norm_num)]; simp
  have m0 : (0 : ℤ) ∈ A := by simp [hA]
  have m1 : (1 : ℤ) ∈ A := by simp [hA]
  have mm1 : (-1 : ℤ) ∈ A := by simp [hA]
  have podd : ∀ m : ℕ, (3 : ℤ) ^ m % 2 = 1 := by
    intro m; exact Int.odd_iff.1 (Odd.pow (by decide))
  have p1 : ∀ m : ℕ, 1 ≤ (3 : ℤ) ^ m := fun m => one_le_pow₀ (by norm_num)
  -- -3 ∈ A
  have m3 : (-3 : ℤ) ∈ A := by
    by_contra h3
    have hm2 : (-2 : ℤ) ∈ A := by
      by_contra hm2
      have := hrel 0 (-1) m0 mm1 (by rw [i0, im1]; omega) (by norm_num)
        (by simpa using hm2) (by simpa using h3)
      omega
    have := hAPC 0 (-1) m0 mm1 (by simpa using hm2) (by rw [i0, im1]; omega)
      (by rw [im1]; have := ige3 (2 * -1 - 0) (by norm_num) (by norm_num) (by norm_num); omega)
    exact h3 (by simpa using this.1)
  have m5 : (-5 : ℤ) ∈ A := by
    have := hAPC 1 (-1) m1 mm1 (by simpa using m3) (by rw [i1, im1]; omega)
      (by rw [im1]; have := ige3 (2 * -1 - 1) (by norm_num) (by norm_num) (by norm_num); omega)
    simpa using this.1
  -- bounds
  have hne : (A.toFinset).Nonempty := ⟨0, by simp [m0]⟩
  set L := A.toFinset.min' hne
  set U := A.toFinset.max' hne
  have hbd : ∀ x ∈ A, L ≤ x ∧ x ≤ U := fun x hx =>
    ⟨Finset.min'_le _ x (List.mem_toFinset.2 hx), Finset.le_max' _ x (List.mem_toFinset.2 hx)⟩
  have hL0 := (hbd 0 m0).1
  have hU0 := (hbd 0 m0).2
  -- generic ray argument
  have ray : ∀ c : ℤ, (c = 1 ∨ c = -1) → ∃ m : ℕ, 1 ≤ m ∧ c * (3 : ℤ) ^ m ∈ A ∧
      c * (3 : ℤ) ^ (m + 1) ∉ A ∧ 2 * c * (3 : ℤ) ^ m ∈ A ∧
      A.idxOf (2 * c * (3 : ℤ) ^ m) < A.idxOf (c * (3 : ℤ) ^ m) := by
    intro c hcpm
    have hex : ∃ m : ℕ, c * (3 : ℤ) ^ (m + 1) ∉ A := by
      refine ⟨(U - L).toNat, fun h => ?_⟩
      have hb := hbd _ h
      have hpow : ((U - L).toNat + 1 : ℤ) < (3 : ℤ) ^ ((U - L).toNat + 1) := by
        have h := Nat.lt_pow_self (n := (U - L).toNat + 1) (a := 3) (by norm_num)
        have h' : (((U - L).toNat + 1 : ℕ) : ℤ) < ((3 ^ ((U - L).toNat + 1) : ℕ) : ℤ) := by
          exact_mod_cast h
        push_cast at h'; exact h'
      rcases hcpm with rfl | rfl <;> omega
    classical
    let m := Nat.find hex
    have hm : c * (3 : ℤ) ^ (m + 1) ∉ A := Nat.find_spec hex
    have hlt : ∀ k < m, c * (3 : ℤ) ^ (k + 1) ∈ A := fun k hk => by
      have := Nat.find_min hex hk; simpa using this
    have hcA : c ∈ A := by rcases hcpm with rfl | rfl <;> assumption
    have hin : c * (3 : ℤ) ^ m ∈ A := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0]; simpa using hcA
      · have := hlt (m - 1) (by omega)
        rwa [Nat.sub_add_cancel h0] at this
    have hpm := p1 m
    have hpo := podd m
    have hne0 : c * (3 : ℤ) ^ m ≠ 0 := by rcases hcpm with rfl | rfl <;> omega
    have hi0 : A.idxOf 0 < A.idxOf (c * (3 : ℤ) ^ m) := by rw [i0]; exact ige1 _ hne0
    have e3 : 3 * (c * (3 : ℤ) ^ m) - 2 * 0 = c * (3 : ℤ) ^ (m + 1) := by ring
    have e2 : 2 * (c * (3 : ℤ) ^ m) - 0 = 2 * c * (3 : ℤ) ^ m := by ring
    have hdbl : 2 * c * (3 : ℤ) ^ m ∈ A := by
      by_contra hd
      have := hrel 0 _ m0 hin hi0 (by rcases hcpm with rfl | rfl <;> omega)
        (by rw [e2]; exact hd) (by rw [e3]; exact hm)
      rcases hcpm with rfl | rfl <;> omega
    have hord : A.idxOf (2 * c * (3 : ℤ) ^ m) < A.idxOf (c * (3 : ℤ) ^ m) := by
      have hneq : 2 * c * (3 : ℤ) ^ m ≠ c * (3 : ℤ) ^ m := by
        rcases hcpm with rfl | rfl <;> omega
      have hni := idx_ne hdbl hneq
      by_contra hge
      have := hAPC 0 _ m0 hin (by rw [e2]; exact hdbl) hi0 (by rw [e2]; omega)
      exact hm (by rw [← e3]; exact this.1)
    refine ⟨m, ?_, hin, hm, hdbl, hord⟩
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0] at hord
    rcases hcpm with rfl | rfl
    · simp only [pow_zero, mul_one] at hord
      rw [i1] at hord
      have := ige2 2 (by norm_num) (by norm_num); omega
    · simp only [pow_zero, mul_one] at hord
      rw [im1] at hord
      have := ige3 (2 * -1) (by norm_num) (by norm_num) (by norm_num); omega
  obtain ⟨m, hm1, a1, a2, a3, a4⟩ := ray 1 (Or.inl rfl)
  obtain ⟨n, hn1, b1, b2, b3, b4⟩ := ray (-1) (Or.inr rfl)
  refine ⟨m3, m5, ⟨m, hm1, by simpa using a1, by simpa using a2, by simpa using a3,
    by simpa using a4⟩, ⟨n, hn1, by simpa using b1, by simpa using b2, ?_, ?_⟩⟩
  · have e : (2 * -1 * (3 : ℤ) ^ n) = -2 * 3 ^ n := by ring
    rw [← e]; exact b3
  · have e : (2 * -1 * (3 : ℤ) ^ n) = -2 * 3 ^ n := by ring
    have e' : (-1 * (3 : ℤ) ^ n) = -3 ^ n := by ring
    rw [← e, ← e']; exact b4

end Erdos195


namespace Erdos195
open E195Tree E195Par

/-- **Exact lifting criterion, root bit TRUE.** -/
theorem lifting_criterion_true (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (S R : List ℤ) (y : ℤ)
    (hS : Safe (treeLt θ) S) (hRe : ∀ r ∈ R, r % 2 = 0) (hy : y % 2 = 1) (hyS : y ∉ S) :
    Safe (treeLt θ) (S ++ R ++ [y]) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        (((S ++ R).filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        (((S ++ [y]).filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ b ∈ R, b ∉ S → ∀ a ∈ S, a % 2 = 1 →
        2 * b - a ∈ S ∨ 2 * b - a = y ∨ 3 * b - 2 * a ∈ S ++ R) ∧
      (∀ a ∈ S, ∀ b ∈ S, (b - a) % 2 = 1 → S.idxOf a < S.idxOf b →
        2 * b - a ∈ R → 2 * b - a ∉ S → 3 * b - 2 * a ∈ S) ∧
      (∀ b ∈ S ++ R, b % 2 = 0 → 2 * b - y ∈ S →
        (S ++ R).idxOf (2 * b - y) < (S ++ R).idxOf b → 2 * y - b ∈ S ++ R) := by
  obtain ⟨-, -, hMS⟩ := (safe_parity_decomp θ S).1 hS
  set P := S ++ R with hP
  set Q := P ++ [y] with hQ
  have hyP : y ∉ P := by
    intro h; rcases List.mem_append.1 h with h | h
    · exact hyS h
    · have := hRe y h; omega
  have memQ : ∀ x, x ∈ Q ↔ x ∈ P ∨ x = y := by intro x; simp [Q]
  have memP : ∀ x, x ∈ P ↔ x ∈ S ∨ x ∈ R := by intro x; simp [P]
  have idxQP : ∀ x ∈ P, Q.idxOf x = P.idxOf x := fun x hx => List.idxOf_append_of_mem hx
  have idxPS : ∀ x ∈ S, P.idxOf x = S.idxOf x := fun x hx => List.idxOf_append_of_mem hx
  have idxQS : ∀ x ∈ S, Q.idxOf x = S.idxOf x := fun x hx =>
    (idxQP x ((memP x).2 (Or.inl hx))).trans (idxPS x hx)
  have idxy : Q.idxOf y = P.length := by
    rw [List.idxOf_append_of_notMem hyP]; simp
  have ltP : ∀ x ∈ P, Q.idxOf x < Q.idxOf y := by
    intro x hx; rw [idxQP x hx, idxy]; exact List.idxOf_lt_length_of_mem hx
  have ltS : ∀ x ∈ S, Q.idxOf x < S.length := by
    intro x hx; rw [idxQS x hx]; exact List.idxOf_lt_length_of_mem hx
  have geS : ∀ x, x ∉ S → S.length ≤ Q.idxOf x := by
    intro x hx
    rw [hQ, hP, List.append_assoc, List.idxOf_append_of_notMem hx]; omega
  have pre : ∀ a b, b ∈ S → Q.idxOf a < Q.idxOf b → a ∈ S := by
    intro a b hb i
    by_contra ha
    have := geS a ha; have := ltS b hb; omega
  have oddQ : ∀ x ∈ Q, x % 2 = 1 → x ∈ S ∨ x = y := by
    intro x hx hxo
    rcases (memQ x).1 hx with h | h
    · rcases (memP x).1 h with h | h
      · exact Or.inl h
      · have := hRe x h; omega
    · exact Or.inr h
  have SQ : ∀ x ∈ S, x ∈ Q := fun x hx => (memQ x).2 (Or.inl ((memP x).2 (Or.inl hx)))
  have SP : ∀ x ∈ S, x ∈ P := fun x hx => (memP x).2 (Or.inl hx)
  have RP : ∀ x ∈ R, x ∈ P := fun x hx => (memP x).2 (Or.inr hx)
  have PQ : ∀ x ∈ P, x ∈ Q := fun x hx => (memQ x).2 (Or.inl hx)
  have evQ : ∀ x ∈ Q, x % 2 = 0 → x ∈ P := by
    intro x hx he
    rcases (memQ x).1 hx with h | h
    · exact h
    · omega
  have hEQ : Q.filter (fun x => decide (x % 2 = 0)) = P.filter (fun x => decide (x % 2 = 0)) := by
    rw [hQ, List.filter_append]
    have : [y].filter (fun x => decide (x % 2 = 0)) = [] := by
      simp only [List.filter_cons, List.filter_nil]; simp [hy]
    rw [this, List.append_nil]
  have hOQ : Q.filter (fun x => decide (x % 2 = 1)) = (S ++ [y]).filter (fun x => decide (x % 2 = 1)) := by
    rw [hQ, hP, List.filter_append, List.filter_append, List.filter_append]
    have : R.filter (fun x => decide (x % 2 = 1)) = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx; have := hRe x hx; simp; omega
    rw [this, List.append_nil]
  constructor
  · -- necessity
    intro hQs
    obtain ⟨hE, hO, hM⟩ := (safe_parity_decomp θ Q).1 hQs
    rw [hEQ] at hE; rw [hOQ] at hO
    refine ⟨hE, hO, ?_, ?_, ?_⟩
    · intro b hbR hbS a haS hao
      have hbe := hRe b hbR
      have i : Q.idxOf a < Q.idxOf b := by have := ltS a haS; have := geS b hbS; omega
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3⟩ := hc
      have n2 : 2 * b - a ∉ Q := by
        intro h; rcases oddQ _ h (by omega) with h | h
        · exact c1 h
        · exact c2 h
      have n3 : 3 * b - 2 * a ∉ Q := by
        intro h; exact c3 (evQ _ h (by omega))
      have := (hM a b (SQ a haS) (PQ b (RP b hbR)) (by omega) i).2 n2 n3
      rw [h00] at this; simp at this; omega
    · intro a haS b hbS hab i hcR hcS
      have hcQ := PQ _ (RP _ hcR)
      have ic : Q.idxOf b < Q.idxOf (2 * b - a) := by
        have := ltS b hbS; have := geS _ hcS; omega
      have := (hM a b (SQ a haS) (SQ b hbS) hab
        (by rw [idxQS a haS, idxQS b hbS]; exact i)).1 hcQ ic
      have hce := hRe _ hcR
      rcases oddQ _ this.1 (by omega) with h | h
      · exact h
      · exfalso
        have := ltP _ (RP _ hcR); rw [← h] at this; omega
    · intro b hbP hbe hxS ix
      have hxQ := SQ _ hxS
      have e1 : 2 * b - (2 * b - y) = y := by ring
      have e2 : 3 * b - 2 * (2 * b - y) = 2 * y - b := by ring
      have := (hM (2 * b - y) b hxQ (PQ b hbP) (by omega)
        (by rw [idxQP _ (SP _ hxS), idxQP _ hbP]; exact ix)).1
        (by rw [e1]; exact (memQ y).2 (Or.inr rfl)) (by rw [e1]; exact ltP b hbP)
      rw [e2, e1] at this
      rcases (memQ _).1 this.1 with h | h
      · exact h
      · exfalso; omega
  · -- sufficiency
    rintro ⟨hE, hO, hT2, hT1, hT3⟩
    refine (safe_parity_decomp θ Q).2 ⟨by rw [hEQ]; exact hE, by rw [hOQ]; exact hO, ?_⟩
    intro a b ha hb hab i
    refine ⟨fun hc ic => ?_, fun nc nd => ?_⟩
    · by_cases hcS : 2 * b - a ∈ S
      · have hbS := pre b _ hcS ic
        have haS := pre a b hbS i
        have := (hMS a b haS hbS hab (by rw [← idxQS a haS, ← idxQS b hbS]; exact i)).1 hcS
          (by rw [← idxQS b hbS, ← idxQS _ hcS]; exact ic)
        refine ⟨SQ _ this.1, ?_⟩
        rw [idxQS _ this.1, idxQS _ hcS]; exact this.2
      · by_cases hcy : 2 * b - a = y
        · -- a odd, b even
          have hao : a % 2 = 1 := by omega
          have hbe : b % 2 = 0 := by omega
          have hbP := evQ b hb hbe
          have haS : a ∈ S := by
            rcases oddQ a ha hao with h | h
            · exact h
            · exfalso; have := ltP b hbP; rw [← h] at this; omega
          have ha' : a = 2 * b - y := by omega
          have hd := hT3 b hbP hbe (by rw [← ha']; exact haS)
            (by rw [← ha', ← idxQP a (SP a haS), ← idxQP b hbP]; exact i)
          have e : 3 * b - 2 * a = 2 * y - b := by rw [ha']; ring
          rw [e, hcy]
          exact ⟨PQ _ hd, ltP _ hd⟩
        · have hcR : 2 * b - a ∈ R := by
            rcases (memQ _).1 hc with h | h
            · rcases (memP _).1 h with h | h
              · exact absurd h hcS
              · exact h
            · exact absurd h hcy
          have hce := hRe _ hcR
          have hbo : b % 2 = 1 := by omega
          have hbS : b ∈ S := by
            rcases oddQ b hb hbo with h | h
            · exact h
            · exfalso
              have := ltP _ (RP _ hcR)
              have h2 : Q.idxOf b = Q.idxOf y := by rw [h]
              omega
          have haS := pre a b hbS i
          have hd := hT1 a haS b hbS hab (by rw [← idxQS a haS, ← idxQS b hbS]; exact i) hcR hcS
          exact ⟨SQ _ hd, by have := ltS _ hd; have := geS _ hcS; omega⟩
    · rw [h00]
      simp only [true_iff]
      by_contra hbo
      have hbe : b % 2 = 0 := by omega
      have hbP := evQ b hb hbe
      have hao : a % 2 = 1 := by omega
      have haS : a ∈ S := by
        rcases oddQ a ha hao with h | h
        · exact h
        · exfalso; have := ltP b hbP; rw [← h] at this; omega
      by_cases hbS : b ∈ S
      · have := (hMS a b haS hbS hab (by rw [← idxQS a haS, ← idxQS b hbS]; exact i)).2
          (fun h => nc (SQ _ h)) (fun h => nd (SQ _ h))
        rw [h00] at this; simp at this; omega
      · have hbR : b ∈ R := by
          rcases (memP b).1 hbP with h | h
          · exact absurd h hbS
          · exact h
        rcases hT2 b hbR hbS a haS hao with h | h | h
        · exact nc (SQ _ h)
        · exact nc (by rw [h]; exact (memQ y).2 (Or.inr rfl))
        · exact nd (PQ _ h)

end Erdos195


open Erdos195 in
theorem solution (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (S R : List ℤ) (y : ℤ)
    (hS : Safe (treeLt θ) S) (hRe : ∀ r ∈ R, r % 2 = 0) (hy : y % 2 = 1) (hyS : y ∉ S) :
    Safe (treeLt θ) (S ++ R ++ [y]) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        (((S ++ R).filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        (((S ++ [y]).filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ b ∈ R, b ∉ S → ∀ a ∈ S, a % 2 = 1 →
        2 * b - a ∈ S ∨ 2 * b - a = y ∨ 3 * b - 2 * a ∈ S ++ R) ∧
      (∀ a ∈ S, ∀ b ∈ S, (b - a) % 2 = 1 → S.idxOf a < S.idxOf b →
        2 * b - a ∈ R → 2 * b - a ∉ S → 3 * b - 2 * a ∈ S) ∧
      (∀ b ∈ S ++ R, b % 2 = 0 → 2 * b - y ∈ S →
        (S ++ R).idxOf (2 * b - y) < (S ++ R).idxOf b → 2 * y - b ∈ S ++ R) := by
  exact Erdos195.lifting_criterion_true θ h00 S R y hS hRe hy hyS

#print axioms solution
