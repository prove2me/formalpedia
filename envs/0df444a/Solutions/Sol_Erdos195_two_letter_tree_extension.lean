-- Prove2me | solution 1 for Erdos195.two_letter_tree_extension
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:17:46.453044+00:00
-- url     : https://prove2.me/submissions/33b1439b-2184-427b-9f64-fa8b06291fe4

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

namespace E195Tree
open Erdos195

lemma par_dvd (x d : ℤ) (k : ℕ) (hd : (2 : ℤ) ^ k ∣ d) :
    ((x + d) / 2 ^ k % 2 = x / 2 ^ k % 2 ↔ (2 : ℤ) ^ (k + 1) ∣ d) := by
  obtain ⟨m, rfl⟩ := hd
  have h0 : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show x + 2 ^ k * m = x + m * 2 ^ k by ring, Int.add_mul_ediv_right _ _ h0, pow_succ,
    mul_dvd_mul_iff_left h0]
  omega

/-- Same-level pairs with congruent first entries mod `2^k` force the same bit iff the first
entries are congruent mod `2^(k+1)`. -/
lemma conflict_iff {a b a' b' : ℤ} (hab : a ≠ b) (hab' : a' ≠ b')
    (hk : padicValInt 2 (b - a) = padicValInt 2 (b' - a'))
    (hd : (2 : ℤ) ^ padicValInt 2 (b - a) ∣ a' - a) :
    ((bitOne b (padicValInt 2 (b - a)) ↔ bitOne b' (padicValInt 2 (b - a))) ↔
      (2 : ℤ) ^ (padicValInt 2 (b - a) + 1) ∣ a' - a) := by
  have d1 := bit_ne hab
  have d2 := bit_ne hab'
  rw [← hk] at d2
  have p := par_dvd a (a' - a) _ hd
  rw [show a + (a' - a) = a' by ring] at p
  unfold bitOne at d1 d2 ⊢
  rw [← p]
  constructor
  · intro h; omega
  · intro h; omega

lemma exists_safe_of (Q : List ℤ) (h1 : APC Q)
    (h2 : ∀ a b a' b' : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
          2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
          a' ∈ Q → b' ∈ Q → Q.idxOf a' < Q.idxOf b' →
          2 * b' - a' ∉ Q → 3 * b' - 2 * a' ∉ Q →
          padicValInt 2 (b - a) = padicValInt 2 (b' - a') →
          (2 : ℤ) ^ padicValInt 2 (b - a) ∣ a' - a →
          (2 : ℤ) ^ (padicValInt 2 (b - a) + 1) ∣ a' - a) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by
  refine (exists_treeLt_safe_iff Q).2 ⟨h1, fun a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk hr => ?_⟩
  have hd : (2 : ℤ) ^ padicValInt 2 (b - a) ∣ a' - a := Int.ModEq.dvd hr
  exact (conflict_iff (ne_of_idx i) (ne_of_idx i') hk hd).2
    (h2 a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk hd)

lemma idxOf_map_inj (f : ℤ → ℤ) (hf : Function.Injective f) (x : ℤ) :
    ∀ P : List ℤ, (P.map f).idxOf (f x) = P.idxOf x := by
  intro P
  induction P with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = x
    · subst h; simp
    · have : f a ≠ f x := fun h' => h (hf h')
      simp [List.idxOf_cons_ne _ h, List.idxOf_cons_ne _ this, ih]

lemma val_mul_odd {u d : ℤ} (hu : Odd u) (hd : d ≠ 0) :
    padicValInt 2 (u * d) = padicValInt 2 d := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [padicValInt.mul hu0 hd]
  have : padicValInt 2 u = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    rintro ⟨c, hc⟩; obtain ⟨e, he⟩ := hu; omega
  omega

lemma dvd_of_dvd_odd_mul {u d : ℤ} (hu : Odd u) {n : ℕ} (h : (2 : ℤ) ^ n ∣ u * d) :
    (2 : ℤ) ^ n ∣ d := by
  have hc : IsCoprime ((2 : ℤ) ^ n) u := (Int.isCoprime_two_left.mpr hu).pow_left
  exact hc.dvd_of_dvd_mul_left h

end E195Tree

namespace Erdos195
open E195Tree

/-- **Affine invariance (Astra tree Thm 3).** -/
theorem treeLt_safe_affine (u v : ℤ) (hu : Odd u) (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (h : Safe (treeLt θ) Q) :
    ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (Q.map (fun x => u * x + v)) := by
  set g : ℤ → ℤ := fun x => u * x + v with hg
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have ginj : Function.Injective g := by
    intro x y hxy
    simp only [hg] at hxy
    exact mul_left_cancel₀ hu0 (by linarith)
  have mem : ∀ x, g x ∈ Q.map g ↔ x ∈ Q := fun x => List.mem_map_of_injective ginj
  have idx : ∀ x, (Q.map g).idxOf (g x) = Q.idxOf x := fun x => idxOf_map_inj g ginj x Q
  have pre : ∀ y ∈ Q.map g, ∃ x ∈ Q, g x = y := fun y hy => List.mem_map.1 hy
  have e2 : ∀ a b, 2 * g b - g a = g (2 * b - a) := fun a b => by simp only [hg]; ring
  have e3 : ∀ a b, 3 * g b - 2 * g a = g (3 * b - 2 * a) := fun a b => by simp only [hg]; ring
  have esub : ∀ a b, g b - g a = u * (b - a) := fun a b => by simp only [hg]; ring
  obtain ⟨h1, h2⟩ := (exists_treeLt_safe_iff Q).1 ⟨θ, h⟩
  apply exists_safe_of
  · intro A B hA hB hC i1 i2
    obtain ⟨a, ha, rfl⟩ := pre A hA
    obtain ⟨b, hb, rfl⟩ := pre B hB
    rw [e2, mem] at hC
    rw [e2, idx, idx] at i2
    rw [idx, idx] at i1
    obtain ⟨m, im⟩ := h1 a b ha hb hC i1 i2
    rw [e3, e2, mem, idx, idx]
    exact ⟨m, im⟩
  · intro A B A' B' hA hB i n2 n3 hA' hB' i' n2' n3' hk hd
    obtain ⟨a, ha, rfl⟩ := pre A hA
    obtain ⟨b, hb, rfl⟩ := pre B hB
    obtain ⟨a', ha', rfl⟩ := pre A' hA'
    obtain ⟨b', hb', rfl⟩ := pre B' hB'
    rw [idx, idx] at i i'
    rw [e2, mem] at n2 n2'
    rw [e3, mem] at n3 n3'
    have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_idx i).symm
    have hne' : b' - a' ≠ 0 := sub_ne_zero.mpr (ne_of_idx i').symm
    rw [esub, esub, val_mul_odd hu hne, val_mul_odd hu hne'] at hk
    rw [esub, esub, val_mul_odd hu hne] at hd ⊢
    have hd' := dvd_of_dvd_odd_mul hu hd
    have c := h2 a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk (emod_eq_of_dvd hd')
    have := (conflict_iff (ne_of_idx i) (ne_of_idx i') hk hd').1 c
    exact this.mul_left u

end Erdos195

namespace E195Tree
open Erdos195

lemma idx3 {p q u : ℤ} (hpq : p ≠ q) (hpu : p ≠ u) (hqu : q ≠ u) :
    [p, q, u].idxOf p = 0 ∧ [p, q, u].idxOf q = 1 ∧ [p, q, u].idxOf u = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [List.idxOf_cons, hpq, hpu, hqu, hpq.symm, hpu.symm, hqu.symm]

lemma idx4 {p q u v : ℤ} (hpq : p ≠ q) (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v)
    (huv : u ≠ v) :
    [p, q, u, v].idxOf p = 0 ∧ [p, q, u, v].idxOf q = 1 ∧ [p, q, u, v].idxOf u = 2 ∧
      [p, q, u, v].idxOf v = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [List.idxOf_cons, hpq, hpu, hpv, hqu, hqv, huv, hpq.symm, hpu.symm, hpv.symm, hqu.symm,
      hqv.symm, huv.symm]

lemma pairs3 {p q u x y : ℤ} (hpq : p ≠ q) (hpu : p ≠ u) (hqu : q ≠ u) (hx : x ∈ [p, q, u])
    (hy : y ∈ [p, q, u]) (h : [p, q, u].idxOf x < [p, q, u].idxOf y) :
    (x = p ∧ y = q) ∨ (x = p ∧ y = u) ∨ (x = q ∧ y = u) := by
  obtain ⟨i0, i1, i2⟩ := idx3 hpq hpu hqu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    (simp only [i0, i1, i2] at h; first | omega | simp)

lemma triples3 {p q u x y z : ℤ} (hpq : p ≠ q) (hpu : p ≠ u) (hqu : q ≠ u) (hx : x ∈ [p, q, u])
    (hy : y ∈ [p, q, u]) (hz : z ∈ [p, q, u]) (h1 : [p, q, u].idxOf x < [p, q, u].idxOf y)
    (h2 : [p, q, u].idxOf y < [p, q, u].idxOf z) : x = p ∧ y = q ∧ z = u := by
  obtain ⟨i0, i1, i2⟩ := idx3 hpq hpu hqu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    (simp only [i0, i1, i2] at h1 h2; first | omega | simp)

lemma pairs4 {p q u v x y : ℤ} (hpq : p ≠ q) (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u)
    (hqv : q ≠ v) (huv : u ≠ v) (hx : x ∈ [p, q, u, v]) (hy : y ∈ [p, q, u, v])
    (h : [p, q, u, v].idxOf x < [p, q, u, v].idxOf y) :
    (x = p ∧ y = q) ∨ (x = p ∧ y = u) ∨ (x = p ∧ y = v) ∨ (x = q ∧ y = u) ∨ (x = q ∧ y = v) ∨
      (x = u ∧ y = v) := by
  obtain ⟨i0, i1, i2, i3⟩ := idx4 hpq hpu hpv hqu hqv huv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    (simp only [i0, i1, i2, i3] at h; first | omega | simp)

lemma triples4 {p q u v x y z : ℤ} (hpq : p ≠ q) (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u)
    (hqv : q ≠ v) (huv : u ≠ v) (hx : x ∈ [p, q, u, v]) (hy : y ∈ [p, q, u, v])
    (hz : z ∈ [p, q, u, v]) (h1 : [p, q, u, v].idxOf x < [p, q, u, v].idxOf y)
    (h2 : [p, q, u, v].idxOf y < [p, q, u, v].idxOf z) :
    (x = p ∧ y = q ∧ z = u) ∨ (x = p ∧ y = q ∧ z = v) ∨ (x = p ∧ y = u ∧ z = v) ∨
      (x = q ∧ y = u ∧ z = v) := by
  obtain ⟨i0, i1, i2, i3⟩ := idx4 hpq hpu hpv hqu hqv huv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl <;>
    (simp only [i0, i1, i2, i3] at h1 h2; first | omega | simp)

lemma val_two_mul {x : ℤ} (hx : x ≠ 0) : padicValInt 2 (2 * x) = padicValInt 2 x + 1 := by
  rw [padicValInt.mul (by norm_num) hx]
  have : padicValInt 2 (2 : ℤ) = 1 := by
    rw [padicValInt]; simp
  omega

/-- Cross lemma: first entries `a,b`, a level different from `ν₂(b-a)`. -/
lemma cross {a b d : ℤ} {m : ℕ} (hab : a ≠ b) (hm : m ≠ padicValInt 2 (b - a))
    (hd : d = b - a ∨ d = a - b) (h : (2 : ℤ) ^ m ∣ d) : (2 : ℤ) ^ (m + 1) ∣ d := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h' : (2 : ℤ) ^ m ∣ b - a := by
    rcases hd with rfl | rfl
    · exact h
    · rw [show b - a = -(a - b) by ring]; exact (dvd_neg).2 h
  have hle := le_val_of_dvd hne h'
  have h2 : (2 : ℤ) ^ (m + 1) ∣ b - a := dvd_of_le_val (by omega)
  rcases hd with rfl | rfl
  · exact h2
  · rw [show a - b = -(b - a) by ring]; exact (dvd_neg).2 h2

end E195Tree

namespace Erdos195
open E195Tree

/-- **Two-letter Tree Extension Lemma (Astra tree2 Thm 1).** -/
theorem two_letter_tree_extension (a b t : ℤ) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      (if padicValInt 2 (b - a) = padicValInt 2 (t - b) then [a, b, 2 * t - b, t]
        else [a, b, t]) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have htb : t - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbt)
  split_ifs with hkl
  · set s := 2 * t - b with hs
    have hsb : s - b = 2 * (t - b) := by rw [hs]; ring
    have vsb : padicValInt 2 (s - b) = padicValInt 2 (b - a) + 1 := by
      rw [hsb, val_two_mul htb, hkl]
    have has : a ≠ s := by
      intro h
      have e : b - a = 2 * (b - t) := by rw [h, hs]; ring
      have hbt' : b - t ≠ 0 := sub_ne_zero.mpr hbt
      have := congrArg (padicValInt 2) e
      rw [val_two_mul hbt', padicValInt_sub_comm b t, ← hkl] at this
      omega
    have hbs : b ≠ s := by intro h; apply hbt; rw [hs] at h; linarith
    have hst : s ≠ t := by intro h; apply hbt; rw [hs] at h; linarith
    apply exists_safe_of
    · intro x y hx hy hz i1 i2
      rcases triples4 hab has hat hbs hbt hst hx hy hz i1 i2 with
        ⟨ex, ey, h⟩ | ⟨ex, ey, h⟩ | ⟨ex, ey, h⟩ | ⟨ex, ey, h⟩ <;> subst x y
      · exfalso
        have : b - a = 2 * (t - b) := by rw [hs] at h; linarith
        rw [this, val_two_mul htb] at hkl; omega
      · have e : 3 * b - 2 * a = s := by rw [hs, ← h]; ring
        rw [e]; obtain ⟨-, -, i2', i3'⟩ := idx4 hab has hat hbs hbt hst
        rw [h] at i2 ⊢
        refine ⟨by simp, ?_⟩; rw [i2', i3']; omega
      · have e : 3 * s - 2 * a = b := by rw [hs] at h ⊢; linarith
        rw [e]; obtain ⟨-, i1', -, i3'⟩ := idx4 hab has hat hbs hbt hst
        rw [h]
        refine ⟨by simp, ?_⟩; rw [i1', i3']; omega
      · exfalso; apply hbt; rw [hs] at h; linarith
    · -- open pairs start at `x` or are `(b, s)`
      have opn : ∀ x y, x ∈ [a, b, s, t] → y ∈ [a, b, s, t] →
          [a, b, s, t].idxOf x < [a, b, s, t].idxOf y → 2 * y - x ∉ [a, b, s, t] →
          x = a ∨ (x = b ∧ y = s) := by
        intro x y hx hy i n2
        rcases pairs4 hab has hat hbs hbt hst hx hy i with
          ⟨ex, -⟩ | ⟨ex, -⟩ | ⟨ex, -⟩ | ⟨ex, ey⟩ | ⟨ex, ey⟩ | ⟨ex, ey⟩
        · exact Or.inl ex
        · exact Or.inl ex
        · exact Or.inl ex
        · exact Or.inr ⟨ex, ey⟩
        · exfalso; apply n2; rw [ex, ey]; simp [hs]
        · exfalso; apply n2; rw [ex, ey, show 2 * t - s = b by rw [hs]; ring]; simp
      intro x y x' y' hx hy i n2 _ hx' hy' i' n2' _ hk hd
      rcases opn x y hx hy i n2 with ex | ⟨ex, ey⟩ <;>
        rcases opn x' y' hx' hy' i' n2' with ex' | ⟨ex', ey'⟩ <;>
        subst x x' <;> (try subst y) <;> (try subst y')
      · simp
      · exact cross hab (by rw [hk, vsb]; omega) (Or.inl rfl) hd
      · exact cross hab (by rw [vsb]; omega) (Or.inr rfl) hd
      · simp
  · apply exists_safe_of
    · intro x y hx hy hz i1 i2
      obtain ⟨ex, ey, h⟩ := triples3 hab hat hbt hx hy hz i1 i2
      subst x y
      exfalso; apply hkl
      rw [← h]; congr 1; ring
    · have opn : ∀ x y, x ∈ [a, b, t] → y ∈ [a, b, t] →
          [a, b, t].idxOf x < [a, b, t].idxOf y → x = a ∨ (x = b ∧ y = t) := by
        intro x y hx hy i
        rcases pairs3 hab hat hbt hx hy i with ⟨ex, -⟩ | ⟨ex, -⟩ | ⟨ex, ey⟩
        · exact Or.inl ex
        · exact Or.inl ex
        · exact Or.inr ⟨ex, ey⟩
      intro x y x' y' hx hy i _ _ hx' hy' i' _ _ hk hd
      rcases opn x y hx hy i with ex | ⟨ex, ey⟩ <;>
        rcases opn x' y' hx' hy' i' with ex' | ⟨ex', ey'⟩ <;>
        subst x x' <;> (try subst y) <;> (try subst y')
      · simp
      · exact cross hab (by rw [hk]; exact fun h => hkl h.symm) (Or.inl rfl) hd
      · exact cross hab (fun h => hkl h.symm) (Or.inr rfl) hd
      · simp

end Erdos195

namespace E195Tree
open Erdos195

lemma prefix_mono {P : ℕ → List ℤ} (hpre : ∀ n, P n <+: P (n + 1)) {m n : ℕ} (h : m ≤ n) :
    P m <+: P n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (hpre n)

lemma len_unbounded {P : ℕ → List ℤ} (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (i : ℕ) : ∃ n, i < (P n).length := by
  induction i with
  | zero =>
    obtain ⟨n, hn⟩ := hcov 0
    exact ⟨n, List.length_pos_of_mem hn⟩
  | succ i ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (P n).toFinset
    rw [List.mem_toFinset] at hx
    obtain ⟨m, hm⟩ := hcov x
    refine ⟨max n m, ?_⟩
    obtain ⟨t, ht⟩ := prefix_mono hpre (le_max_left n m)
    have hxM : x ∈ P (max n m) := (prefix_mono hpre (le_max_right n m)).subset hm
    rw [← ht] at hxM
    have ht0 : t ≠ [] := by
      rintro rfl; simp at hxM; exact hx hxM
    have : 0 < t.length := List.length_pos_iff.2 ht0
    rw [← ht, List.length_append]
    omega

lemma get_stable {P : ℕ → List ℤ} (hpre : ∀ n, P n <+: P (n + 1)) {m n i : ℕ}
    (hm : i < (P m).length) (hn : i < (P n).length) : (P m)[i] = (P n)[i] := by
  rcases le_total m n with h | h
  · exact ((prefix_mono hpre h).getElem hm).symm ▸ rfl
  · exact ((prefix_mono hpre h).getElem hn) ▸ rfl

end E195Tree

namespace Erdos195
open E195Tree

/-- **Limit lemma (L), for arbitrary (stage-dependent) completion orders.** -/
theorem exists_perm_of_safe_chain (R : ℕ → ℤ → ℤ → Prop) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (R n) (P n)) (hnd : ∀ n, (P n).Nodup)
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x : ℤ, ∃ n, x ∈ P n) :
    ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 := by
  classical
  have hub := len_unbounded hpre hcov
  choose N hN using hub
  let g : ℕ → ℤ := fun i => (P (N i))[i]'(hN i)
  have hg : ∀ n i (h : i < (P n).length), g i = (P n)[i] := fun n i h => get_stable hpre (hN i) h
  have ginj : Function.Injective g := by
    intro i j hij
    set n := max (N i) (N j)
    have hi : i < (P n).length :=
      lt_of_lt_of_le (hN i) ((prefix_mono hpre (le_max_left _ _)).length_le)
    have hj : j < (P n).length :=
      lt_of_lt_of_le (hN j) ((prefix_mono hpre (le_max_right _ _)).length_le)
    rw [hg n i hi, hg n j hj] at hij
    exact (List.Nodup.getElem_inj_iff (hnd n)).1 hij
  have gsurj : Function.Surjective g := by
    intro x
    obtain ⟨n, hn⟩ := hcov x
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
    exact ⟨i, hg n i hi⟩
  refine ⟨Equiv.ofBijective g ⟨ginj, gsurj⟩, ?_⟩
  rintro ⟨l, ⟨a, d, hAP⟩, hl⟩
  have hlen : l.length = 4 := by
    have : (l.map (Equiv.ofBijective g ⟨ginj, gsurj⟩)).length = 4 := by
      rcases hAP with h | h <;> rw [h] <;> simp
    simpa using this
  match l, hlen, hl, hAP with
  | [i, j, k, m], _, hl, hAP =>
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hl
    obtain ⟨⟨hij, hik, him⟩, ⟨hjk, hjm⟩, hkm, -⟩ := hl
    set n := N m
    have hm : m < (P n).length := hN m
    have hi : i < (P n).length := by omega
    have hj : j < (P n).length := by omega
    have hk : k < (P n).length := by omega
    have cl : ∀ p q (hp : p < (P n).length) (hq : q < (P n).length), p < q →
        compLt (R n) (P n) ((P n)[p]) ((P n)[q]) := by
      intro p q hp hq hpq
      refine Or.inl ⟨List.getElem_mem hp, List.getElem_mem hq, ?_⟩
      rw [List.Nodup.idxOf_getElem (hnd n), List.Nodup.idxOf_getElem (hnd n)]
      exact hpq
    have fi := hg n i hi
    have fj := hg n j hj
    have fk := hg n k hk
    have fm := hg n m hm
    have gne : g i ≠ g j := fun h => by have := ginj h; omega
    simp only [List.map_cons, List.map_nil] at hAP
    rcases hAP with h | h
    · simp [List.range_succ] at h
      obtain ⟨e0, e1, e2, e3⟩ := h
      replace e0 : g i = _ := e0
      replace e1 : g j = _ := e1
      replace e2 : g k = _ := e2
      replace e3 : g m = _ := e3
      have hd : d ≠ 0 := by rintro rfl; apply gne; rw [e0, e1]; simp
      apply hsafe n (g i) d hd
      refine ⟨?_, ?_, ?_⟩
      · rw [show g i + d = g j by rw [e0, e1] <;> ring, fi, fj]; exact cl i j hi hj hij
      · rw [show g i + d = g j by rw [e0, e1] <;> ring, show g i + 2 * d = g k by rw [e0, e2] <;> ring,
          fj, fk]; exact cl j k hj hk hjk
      · rw [show g i + 2 * d = g k by rw [e0, e2] <;> ring, show g i + 3 * d = g m by rw [e0, e3] <;> ring,
          fk, fm]; exact cl k m hk hm hkm
    · simp [List.range_succ] at h
      obtain ⟨e0, e1, e2, e3⟩ := h
      replace e0 : g i = _ := e0
      replace e1 : g j = _ := e1
      replace e2 : g k = _ := e2
      replace e3 : g m = _ := e3
      have hd : -d ≠ 0 := by
        intro h0; apply gne; rw [e0, e1]; have : d = 0 := by linarith
        subst this; simp
      apply hsafe n (g i) (-d) hd
      refine ⟨?_, ?_, ?_⟩
      · rw [show g i + -d = g j by rw [e0, e1] <;> ring, fi, fj]; exact cl i j hi hj hij
      · rw [show g i + -d = g j by rw [e0, e1] <;> ring, show g i + 2 * -d = g k by rw [e0, e2] <;> ring,
          fj, fk]; exact cl j k hj hk hjk
      · rw [show g i + 2 * -d = g k by rw [e0, e2] <;> ring, show g i + 3 * -d = g m by rw [e0, e3] <;> ring,
          fk, fm]; exact cl k m hk hm hkm

/-- **Tree limit lemma.** Nested tree-safe words (any witnesses, possibly varying with the stage)
covering `ℤ` give a bijection `ℕ ≃ ℤ` with no monotone 4-AP. -/
theorem exists_perm_of_tree_safe_chain (θ : ℕ → ℕ → ℤ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (treeLt (θ n)) (P n)) (hnd : ∀ n, (P n).Nodup)
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x : ℤ, ∃ n, x ∈ P n) :
    ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 :=
  exists_perm_of_safe_chain (fun n => treeLt (θ n)) P hsafe hnd hpre hcov

end Erdos195

namespace Erdos195
open E195Tree

/-- **No finite closure under fourth terms (Astra tree Prop 5).** -/
theorem no_finite_fourth_term_closed (Q : List ℤ) (hQ : ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y) :
    ∃ a b : ℤ, a ∈ Q ∧ b ∈ Q ∧ Q.idxOf a < Q.idxOf b ∧ 3 * b - 2 * a ∉ Q := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hQ
  have hne : Q.toFinset.Nonempty := ⟨x, List.mem_toFinset.2 hx⟩
  set A := Q.toFinset.min' hne
  set B := Q.toFinset.max' hne
  have hA : A ∈ Q := List.mem_toFinset.1 (Finset.min'_mem _ _)
  have hB : B ∈ Q := List.mem_toFinset.1 (Finset.max'_mem _ _)
  have lo : ∀ z ∈ Q, A ≤ z := fun z hz => Finset.min'_le _ z (List.mem_toFinset.2 hz)
  have hi : ∀ z ∈ Q, z ≤ B := fun z hz => Finset.le_max' _ z (List.mem_toFinset.2 hz)
  have hAB : A < B := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact lt_of_le_of_lt (lo x hx) (lt_of_lt_of_le h (hi y hy))
    · exact lt_of_le_of_lt (lo y hy) (lt_of_lt_of_le h (hi x hx))
  have hidx : Q.idxOf A ≠ Q.idxOf B := idx_ne hA (ne_of_lt hAB)
  rcases lt_or_gt_of_ne hidx with h | h
  · exact ⟨A, B, hA, hB, h, fun hm => by have := hi _ hm; linarith⟩
  · exact ⟨B, A, hB, hA, h, fun hm => by have := lo _ hm; linarith⟩

end Erdos195

namespace Erdos195
open E195Tree

/-- **Tree append criterion (Astra tree2 Thm 2).** -/
theorem tree_append_iff (P : List ℤ) (t : ℤ) (hP : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) P)
    (ht : t ∉ P) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P ++ [t])) ↔
      (∀ a b : ℤ, a ∈ P → b ∈ P → P.idxOf a < P.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ P) ∧
      (∀ x a b : ℤ, x ∈ P → 2 * t - x ∉ P → 3 * t - 2 * x ∉ P →
          a ∈ P → b ∈ P → P.idxOf a < P.idxOf b → 2 * b - a ∉ P → 3 * b - 2 * a ∉ P →
          t ≠ 2 * b - a → t ≠ 3 * b - 2 * a →
          padicValInt 2 (b - a) = padicValInt 2 (t - x) →
          a % 2 ^ padicValInt 2 (b - a) = x % 2 ^ padicValInt 2 (b - a) →
          (bitOne b (padicValInt 2 (b - a)) ↔ bitOne t (padicValInt 2 (b - a)))) := by
  set Q := P ++ [t] with hQ
  have mem : ∀ z, z ∈ Q ↔ z ∈ P ∨ z = t := fun z => by simp [hQ]
  have idxP : ∀ z, z ∈ P → Q.idxOf z = P.idxOf z := fun z hz => List.idxOf_append_of_mem hz
  have idxt : Q.idxOf t = P.length := by
    rw [hQ, List.idxOf_append_of_notMem ht]; simp
  have ltl : ∀ z, z ∈ P → P.idxOf z < P.length := fun z hz => List.idxOf_lt_length_of_mem hz
  -- every member of Q has index ≤ length P
  have idxle : ∀ z, z ∈ Q → Q.idxOf z ≤ P.length := by
    intro z hz
    rcases (mem z).1 hz with h | rfl
    · rw [idxP z h]; exact (ltl z h).le
    · rw [idxt]
  -- first entry of an in-order pair of Q lies in P
  have firstP : ∀ a b, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → a ∈ P := by
    intro a b ha hb i
    rcases (mem a).1 ha with h | rfl
    · exact h
    · rw [idxt] at i; have := idxle b hb; omega
  have nt2 : ∀ x, x ≠ t → 2 * t - x ≠ t := fun x hx h => hx (by linarith)
  have nt3 : ∀ x, x ≠ t → 3 * t - 2 * x ≠ t := fun x hx h => hx (by linarith)
  have neP : ∀ x, x ∈ P → x ≠ t := fun x hx h => ht (h ▸ hx)
  constructor
  · rintro hQs
    obtain ⟨h1, h2⟩ := (exists_treeLt_safe_iff Q).1 hQs
    refine ⟨fun a b ha hb i e => ?_, fun x a b hx n2x n3x ha hb i n2 n3 t2 t3 hk hr => ?_⟩
    · have hbt : Q.idxOf b < Q.idxOf (2 * b - a) := by
        rw [← e, idxt, idxP b hb]; exact ltl b hb
      have hab' : Q.idxOf a < Q.idxOf b := by rw [idxP a ha, idxP b hb]; exact i
      obtain ⟨m3, i3⟩ := h1 a b ((mem a).2 (Or.inl ha)) ((mem b).2 (Or.inl hb))
        ((mem _).2 (Or.inr e.symm)) hab' hbt
      rcases (mem _).1 m3 with h | h
      · exact h
      · rw [h, ← e] at i3; exact absurd i3 (lt_irrefl _)
    · have c := h2 a b x t ((mem a).2 (Or.inl ha)) ((mem b).2 (Or.inl hb))
        (by rw [idxP a ha, idxP b hb]; exact i)
        (by rw [mem]; rintro (h | h); exact n2 h; exact t2 h.symm)
        (by rw [mem]; rintro (h | h); exact n3 h; exact t3 h.symm)
        ((mem x).2 (Or.inl hx)) ((mem t).2 (Or.inr rfl))
        (by rw [idxP x hx, idxt]; exact ltl x hx)
        (by rw [mem]; rintro (h | h); exact n2x h; exact nt2 x (neP x hx) h)
        (by rw [mem]; rintro (h | h); exact n3x h; exact nt3 x (neP x hx) h)
        hk hr
      exact c
  · rintro ⟨c1, c2⟩
    obtain ⟨h1, h2⟩ := (exists_treeLt_safe_iff P).1 hP
    apply (exists_treeLt_safe_iff Q).2
    refine ⟨fun a b ha hb hc i1 i2 => ?_, ?_⟩
    · have aP := firstP a b ha hb i1
      have bP := firstP b _ hb hc i2
      rw [idxP a aP, idxP b bP] at i1
      rw [idxP b bP] at i2
      rcases (mem _).1 hc with cP | ct
      · rw [idxP _ cP] at i2
        obtain ⟨m3, i3⟩ := h1 a b aP bP cP i1 i2
        refine ⟨(mem _).2 (Or.inl m3), ?_⟩
        rw [idxP _ m3, idxP _ cP]; exact i3
      · have m3 := c1 a b aP bP i1 ct.symm
        refine ⟨(mem _).2 (Or.inl m3), ?_⟩
        rw [idxP _ m3, ct, idxt]; exact ltl _ m3
    · intro a b a' b' ha hb i n2 n3 ha' hb' i' n2' n3' hk hr
      have aP := firstP a b ha hb i
      have aP' := firstP a' b' ha' hb' i'
      have n2P : 2 * b - a ∉ P := fun h => n2 ((mem _).2 (Or.inl h))
      have n3P : 3 * b - 2 * a ∉ P := fun h => n3 ((mem _).2 (Or.inl h))
      have n2P' : 2 * b' - a' ∉ P := fun h => n2' ((mem _).2 (Or.inl h))
      have n3P' : 3 * b' - 2 * a' ∉ P := fun h => n3' ((mem _).2 (Or.inl h))
      have t2 : t ≠ 2 * b - a := fun h => n2 ((mem _).2 (Or.inr h.symm))
      have t3 : t ≠ 3 * b - 2 * a := fun h => n3 ((mem _).2 (Or.inr h.symm))
      have t2' : t ≠ 2 * b' - a' := fun h => n2' ((mem _).2 (Or.inr h.symm))
      have t3' : t ≠ 3 * b' - 2 * a' := fun h => n3' ((mem _).2 (Or.inr h.symm))
      rcases (mem b).1 hb with bP | rfl <;> rcases (mem b').1 hb' with bP' | rfl
      · rw [idxP a aP, idxP b bP] at i
        rw [idxP a' aP', idxP b' bP'] at i'
        exact h2 a b a' b' aP bP i n2P n3P aP' bP' i' n2P' n3P' hk hr
      · rw [idxP a aP, idxP b bP] at i
        exact c2 a' a b aP' (by rw [two_mul] at n2'; simpa [two_mul] using n2P')
          n3P' aP bP i n2P n3P t2 t3 hk hr
      · rw [idxP a' aP', idxP b' bP'] at i'
        have hr' : a' % 2 ^ padicValInt 2 (b' - a') = a % 2 ^ padicValInt 2 (b' - a') := by
          rw [← hk]; exact hr.symm
        rw [hk]
        exact (c2 a a' b' aP n2P n3P aP' bP' i' n2P' n3P' t2' t3' hk.symm hr').symm
      · exact Iff.rfl

end Erdos195


open Erdos195 in
theorem solution (a b t : ℤ) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      (if padicValInt 2 (b - a) = padicValInt 2 (t - b) then [a, b, 2 * t - b, t]
        else [a, b, t]) := by
  apply Erdos195.two_letter_tree_extension <;> assumption

