-- Prove2me | solution 1 for Erdos195.single_inversion_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T20:29:50.18037+00:00
-- url     : https://prove2.me/submissions/aff10569-3a09-4501-a79f-d460170127fe

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
namespace E195S66
open Erdos195 E195Tree E195Par

lemma exists_safe_scale (k : ℕ) (L : List ℤ) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L) ↔
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (L.map (fun u => (2 : ℤ) ^ k * u)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : L.map (fun u => (2 : ℤ) ^ (k + 1) * u) =
        (L.map (fun u => (2 : ℤ) ^ k * u)).map (fun y => 2 * y + 0) := by
      rw [List.map_map]; congr 1; funext u; simp only [Function.comp]; ring
    rw [e, ih]
    constructor
    · rintro ⟨θ, h⟩
      let θ'' : ℕ → ℤ → Bool := fun j r => match j with
        | 0 => false
        | j + 1 => θ j (r / 2)
      refine ⟨θ'', (safe_map_iff θ'' 0 (Or.inl rfl) _).2 ?_⟩
      have : (fun j r => θ'' (j + 1) (2 * r + 0)) = θ := by
        funext j r; simp only [θ'']; congr 1; omega
      rw [this]; exact h
    · rintro ⟨θ, h⟩
      exact ⟨_, (safe_map_iff θ 0 (Or.inl rfl) _).1 h⟩

lemma exists_safe_trans_mp (a : ℤ) (L : List ℤ) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L) →
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (L.map (fun u => u + a)) := by
  rintro ⟨θ, h⟩
  obtain ⟨θ', hs⟩ := (safe_odd_affine_iff θ 1 a (by norm_num)).1
  have := (((safe_odd_affine_iff θ 1 a (by norm_num)).2 θ' hs).2 L).1 h
  simp only [one_mul] at this
  exact ⟨θ', this⟩

lemma exists_safe_trans (a : ℤ) (L : List ℤ) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L) ↔
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (L.map (fun u => u + a)) := by
  refine ⟨exists_safe_trans_mp a L, fun h => ?_⟩
  have := exists_safe_trans_mp (-a) _ h
  rw [List.map_map] at this
  have e : ((fun u => u + -a) ∘ fun u => u + a) = id := by funext u; simp
  rw [e, List.map_id] at this; exact this

lemma exists_safe_aff (k : ℕ) (a : ℤ) (L : List ℤ) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L) ↔
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (L.map (fun u => (2 : ℤ) ^ k * u + a)) := by
  have e : L.map (fun u => (2 : ℤ) ^ k * u + a) =
      (L.map (fun u => (2 : ℤ) ^ k * u)).map (fun u => u + a) := by
    rw [List.map_map]; rfl
  rw [e, ← exists_safe_trans, ← exists_safe_scale]

end E195S66

namespace E195W
open Erdos195 E195Tree

/-- `Good` without the release clause. -/
def GoodS (Q : List ℤ) : Prop :=
  (∀ a ∈ Q, ∀ b ∈ Q, 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b → Q.idxOf b < Q.idxOf (2 * b - a) →
      3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
  (∀ a ∈ Q, ∀ b ∈ Q, Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
     (b - a) % 2 ^ (vv (b - a)) = 0 ∧ (b - a) / 2 ^ (vv (b - a)) % 2 = 1 ∧
     (thetaOf Q (vv (b - a)) (a % 2 ^ (vv (b - a))) = true ↔ b / 2 ^ (vv (b - a)) % 2 = 1))

instance (Q : List ℤ) : Decidable (GoodS Q) := by unfold GoodS; infer_instance

theorem goodS_sound (Q : List ℤ) (h : GoodS Q) : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨thetaOf Q, (treeLt_safe_iff _ Q).2 ⟨fun a b ha hb hc i1 i2 => h1 a ha b hb hc i1 i2, ?_⟩⟩
  intro a b ha hb i n2 n3
  obtain ⟨c1, c2, c3⟩ := h2 a ha b hb i n2 n3
  rw [val_eq_of_cert c1 c2]; exact c3

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

namespace E195S68
open Erdos195 E195Tree E195Par E195W

lemma idxOf_getElem_le (l : List ℤ) (n : ℕ) (hn : n < l.length) : l.idxOf l[n] ≤ n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n < l.length := by simpa using hn
      simp only [List.getElem_cons_succ, List.idxOf_cons]
      have := ih n hn'
      cases (a == l[n]) <;> simp <;> omega

/-- index-form criterion for the cross 3-AP condition -/
lemma triple_of_get {L : List ℤ} {P : ℤ → ℤ → Prop}
    (h : ∀ i j m (hi : i < L.length) (hj : j < L.length) (hm : m < L.length), i < j → j < m →
      P L[i] L[j] → 2 * L[j] - L[i] = L[m] →
      ∃ n, ∃ hn : n < L.length, n < m ∧ L[n] = 3 * L[j] - 2 * L[i]) :
    ∀ a b, a ∈ L → b ∈ L → P a b → 2 * b - a ∈ L → L.idxOf a < L.idxOf b →
      L.idxOf b < L.idxOf (2 * b - a) →
      3 * b - 2 * a ∈ L ∧ L.idxOf (3 * b - 2 * a) < L.idxOf (2 * b - a) := by
  intro a b ha hb hP hc i1 i2
  have ha' := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  have hc' := List.idxOf_lt_length_of_mem hc
  have hP' : P L[L.idxOf a] L[L.idxOf b] := by rw [List.getElem_idxOf, List.getElem_idxOf]; exact hP
  obtain ⟨n, hn, hnm, e⟩ := h _ _ _ ha' hb' hc' i1 i2 hP' (by
    rw [List.getElem_idxOf, List.getElem_idxOf, List.getElem_idxOf])
  rw [List.getElem_idxOf, List.getElem_idxOf] at e
  rw [← e]
  exact ⟨List.getElem_mem hn, lt_of_le_of_lt (idxOf_getElem_le L n hn) hnm⟩

lemma pairs_of_get {L : List ℤ} {P : ℤ → ℤ → Prop}
    (h : ∀ i j (hi : i < L.length) (hj : j < L.length), i < j → P L[i] L[j]) :
    ∀ a b, a ∈ L → b ∈ L → L.idxOf a < L.idxOf b → P a b := by
  intro a b ha hb hab
  have ha' := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  have := h _ _ ha' hb' hab
  rwa [List.getElem_idxOf, List.getElem_idxOf] at this

/-- **Two-child decomposition at level `h`.** -/
theorem two_child (h : ℕ) (W : List ℤ) (ρ α0 α1 : ℤ)
    (hall : ∀ x ∈ W, x % 2 ^ h = ρ % 2 ^ h)
    (hcov : ∀ x ∈ W, x % 2 ^ (h + 1) = α0 ∨ x % 2 ^ (h + 1) = α1)
    (h0 : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (W.filter (fun x => decide (x % 2 ^ (h + 1) = α0))))
    (h1 : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (W.filter (fun x => decide (x % 2 ^ (h + 1) = α1))))
    (hX1 : ∀ x z, x ∈ W → z ∈ W → x % 2 ^ (h + 1) ≠ z % 2 ^ (h + 1) → 2 * z - x ∈ W →
       W.idxOf x < W.idxOf z → W.idxOf z < W.idxOf (2 * z - x) →
       3 * z - 2 * x ∈ W ∧ W.idxOf (3 * z - 2 * x) < W.idxOf (2 * z - x))
    (hX2 : ∀ x z x' z', x ∈ W → z ∈ W → W.idxOf x < W.idxOf z → 2 * z - x ∉ W →
       3 * z - 2 * x ∉ W → x % 2 ^ (h + 1) ≠ z % 2 ^ (h + 1) →
       x' ∈ W → z' ∈ W → W.idxOf x' < W.idxOf z' → 2 * z' - x' ∉ W → 3 * z' - 2 * x' ∉ W →
       x' % 2 ^ (h + 1) ≠ z' % 2 ^ (h + 1) → (bitOne z h ↔ bitOne z' h)) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) W := by
  obtain ⟨A1, A2⟩ := (exists_treeLt_safe_iff _).1 h0
  obtain ⟨B1, B2⟩ := (exists_treeLt_safe_iff _).1 h1
  have cross_val : ∀ x z, x ∈ W → z ∈ W → x % 2 ^ (h + 1) ≠ z % 2 ^ (h + 1) →
      padicValInt 2 (z - x) = h := by
    intro x z hx hz hne
    have hd : (2 : ℤ) ^ h ∣ z - x := Int.ModEq.dvd ((hall x hx).trans (hall z hz).symm)
    have hz0 : z - x ≠ 0 := by
      intro e; apply hne; rw [show z = x by linarith]
    apply le_antisymm
    · by_contra hc
      have := dvd_of_le_val (show h + 1 ≤ padicValInt 2 (z - x) by omega)
      exact hne (emod_eq_of_dvd this)
    · exact le_val_of_dvd hz0 hd
  have same_val : ∀ x z, W.idxOf x < W.idxOf z → x % 2 ^ (h + 1) = z % 2 ^ (h + 1) →
      h + 1 ≤ padicValInt 2 (z - x) := by
    intro x z i e
    have hz0 : z - x ≠ 0 := sub_ne_zero.2 (Ne.symm (ne_of_idx i))
    exact le_val_of_dvd hz0 (Int.ModEq.dvd e)
  rw [exists_treeLt_safe_iff]
  constructor
  · intro x z hx hz hc i1 i2
    by_cases hs : x % 2 ^ (h + 1) = z % 2 ^ (h + 1)
    · rcases hcov x hx with e | e
      · have pz : z % 2 ^ (h + 1) = α0 := hs.symm.trans e
        exact (C1_filter (closed_mod _ _) W (decide_eq_true e) (decide_eq_true pz)).1
          (fun ha hb hc i1 i2 => A1 x z ha hb hc i1 i2) hx hz hc i1 i2
      · have pz : z % 2 ^ (h + 1) = α1 := hs.symm.trans e
        exact (C1_filter (closed_mod _ _) W (decide_eq_true e) (decide_eq_true pz)).1
          (fun ha hb hc i1 i2 => B1 x z ha hb hc i1 i2) hx hz hc i1 i2
    · exact hX1 x z hx hz hs hc i1 i2
  · intro x z x' z' hx hz i n2 n3 hx' hz' i' n2' n3' hk hr
    by_cases hs : x % 2 ^ (h + 1) = z % 2 ^ (h + 1) <;>
      by_cases hs' : x' % 2 ^ (h + 1) = z' % 2 ^ (h + 1)
    · have v1 := same_val x z i hs
      have hxx : x % 2 ^ (h + 1) = x' % 2 ^ (h + 1) :=
        emod_eq_of_dvd ((pow_dvd_pow 2 v1).trans (Int.ModEq.dvd hr))
      have key : ∀ α : ℤ, x % 2 ^ (h + 1) = α →
          (∀ a b a' b' : ℤ, a ∈ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            b ∈ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            (W.filter (fun x => decide (x % 2 ^ (h + 1) = α))).idxOf a <
              (W.filter (fun x => decide (x % 2 ^ (h + 1) = α))).idxOf b →
            2 * b - a ∉ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            3 * b - 2 * a ∉ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            a' ∈ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            b' ∈ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            (W.filter (fun x => decide (x % 2 ^ (h + 1) = α))).idxOf a' <
              (W.filter (fun x => decide (x % 2 ^ (h + 1) = α))).idxOf b' →
            2 * b' - a' ∉ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            3 * b' - 2 * a' ∉ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) →
            padicValInt 2 (b - a) = padicValInt 2 (b' - a') →
            a % 2 ^ padicValInt 2 (b - a) = a' % 2 ^ padicValInt 2 (b - a) →
            (bitOne b (padicValInt 2 (b - a)) ↔ bitOne b' (padicValInt 2 (b - a)))) →
          (bitOne z (padicValInt 2 (z - x)) ↔ bitOne z' (padicValInt 2 (z - x))) := by
        intro α ex HA
        have pz : z % 2 ^ (h + 1) = α := hs.symm.trans ex
        have px' : x' % 2 ^ (h + 1) = α := hxx.symm.trans ex
        have pz' : z' % 2 ^ (h + 1) = α := hs'.symm.trans px'
        have mf : ∀ v, v ∈ W → v % 2 ^ (h + 1) = α →
            v ∈ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) :=
          fun v hv e => List.mem_filter.2 ⟨hv, decide_eq_true e⟩
        have nf : ∀ v, v ∉ W → v ∉ W.filter (fun x => decide (x % 2 ^ (h + 1) = α)) :=
          fun v hv hm => hv (List.mem_of_mem_filter hm)
        exact HA x z x' z' (mf x hx ex) (mf z hz pz)
          ((idx_filter _ (decide_eq_true ex) (decide_eq_true pz) W).2 i) (nf _ n2) (nf _ n3)
          (mf x' hx' px') (mf z' hz' pz')
          ((idx_filter _ (decide_eq_true px') (decide_eq_true pz') W).2 i') (nf _ n2') (nf _ n3')
          hk hr
      rcases hcov x hx with e | e
      · exact key α0 e A2
      · exact key α1 e B2
    · have := same_val x z i hs
      have := cross_val x' z' hx' hz' hs'
      omega
    · have := cross_val x z hx hz hs
      have := same_val x' z' i' hs'
      omega
    · rw [cross_val x z hx hz hs]
      exact hX2 x z x' z' hx hz i n2 n3 hs hx' hz' i' n2' n3' hs'

/-- **Block separation.** -/
theorem block_sep (h : ℕ) (P S : List ℤ) (ρ α0 α1 : ℤ) (hne : α0 ≠ α1)
    (hall : ∀ x ∈ P ++ S, x % 2 ^ h = ρ % 2 ^ h)
    (hP : ∀ x ∈ P, x % 2 ^ (h + 1) = α0) (hS : ∀ x ∈ S, x % 2 ^ (h + 1) = α1)
    (sP : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) P) (sS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) S) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P ++ S) := by
  have SP : ∀ v ∈ S, v ∉ P := fun v hv hp => hne ((hP v hp).symm.trans (hS v hv))
  have iP : ∀ v ∈ P, (P ++ S).idxOf v < P.length := by
    intro v hv; rw [List.idxOf_append_of_mem hv]; exact List.idxOf_lt_length_of_mem hv
  have iS : ∀ v ∈ S, P.length ≤ (P ++ S).idxOf v := by
    intro v hv; rw [List.idxOf_append_of_notMem (SP v hv)]; omega
  have cls : ∀ v ∈ P ++ S, (v ∈ P ∧ v % 2 ^ (h + 1) = α0) ∨ (v ∈ S ∧ v % 2 ^ (h + 1) = α1) := by
    intro v hv
    rcases List.mem_append.1 hv with e | e
    · exact Or.inl ⟨e, hP v e⟩
    · exact Or.inr ⟨e, hS v e⟩
  apply two_child h (P ++ S) ρ α0 α1 hall
  · intro x hx; rcases cls x hx with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr e
  · rw [List.filter_append, List.filter_eq_self.2 (fun v hv => decide_eq_true (hP v hv)),
      List.filter_eq_nil_iff.2 (fun v hv e => hne ((of_decide_eq_true e).symm.trans (hS v hv))),
      List.append_nil]
    exact sP
  · rw [List.filter_append, List.filter_eq_self.2 (fun v hv => decide_eq_true (hS v hv)),
      List.filter_eq_nil_iff.2 (fun v hv e => hne ((hP v hv).symm.trans (of_decide_eq_true e))),
      List.nil_append]
    exact sS
  · intro x z hx hz hs hc i1 i2
    exfalso
    rcases cls x hx with ⟨xP, ex⟩ | ⟨xS, ex⟩ <;> rcases cls z hz with ⟨zP, ez⟩ | ⟨zS, ez⟩
    · exact hs (ex.trans ez.symm)
    · -- x ∈ P, z ∈ S: 2z - x is in x's child
      have hd : (2 : ℤ) ^ h ∣ z - x := Int.ModEq.dvd ((hall x hx).trans (hall z hz).symm)
      have hd2 : (2 : ℤ) ^ (h + 1) ∣ (2 * z - x) - x := by
        obtain ⟨t, ht⟩ := hd; exact ⟨t, by rw [pow_succ]; linear_combination 2 * ht⟩
      have ec : x % 2 ^ (h + 1) = (2 * z - x) % 2 ^ (h + 1) := emod_eq_of_dvd hd2
      rcases cls _ hc with ⟨cP, -⟩ | ⟨-, ec'⟩
      · have := iP _ cP; have := iS z zS; omega
      · exact hne (ex.symm.trans (ec.trans ec'))
    · have := iP z zP; have := iS x xS; omega
    · exact hs (ex.trans ez.symm)
  · intro x z x' z' hx hz i n2 n3 hs hx' hz' i' n2' n3' hs'
    have zS : ∀ x z, x ∈ P ++ S → z ∈ P ++ S → (P ++ S).idxOf x < (P ++ S).idxOf z →
        x % 2 ^ (h + 1) ≠ z % 2 ^ (h + 1) → z % 2 ^ (h + 1) = α1 := by
      intro x z hx hz i hs
      rcases cls x hx with ⟨xP, ex⟩ | ⟨xS, ex⟩ <;> rcases cls z hz with ⟨zP, ez⟩ | ⟨zS, ez⟩
      · exact absurd (ex.trans ez.symm) hs
      · exact ez
      · have := iP z zP; have := iS x xS; omega
      · exact ez
    have e1 := zS x z hx hz i hs
    have e2 := zS x' z' hx' hz' i' hs'
    unfold bitOne
    rw [digit_eq_of_dvd (Int.ModEq.dvd (e1.trans e2.symm))]

lemma pair_safe (u v : ℤ) (huv : u ≠ v) : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [u, v] := by
  have i0 : [u, v].idxOf u = 0 := by simp
  have i1 : [u, v].idxOf v = 1 := by rw [List.idxOf_cons_ne _ huv]; simp
  rw [exists_treeLt_safe_iff]
  constructor
  · intro x z hx hz hc i1' i2'
    have := List.idxOf_lt_length_of_mem hc
    simp only [List.length_cons, List.length_nil] at this
    omega
  · intro x z x' z' hx hz i n2 n3 hx' hz' i' n2' n3' hk hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz hx' hz'
    rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;> rcases hx' with rfl | rfl <;>
      rcases hz' with rfl | rfl <;> first | exact Iff.rfl | omega

lemma single_safe (u : ℤ) : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [u] := by
  rw [exists_treeLt_safe_iff]
  constructor
  · intro x z hx hz hc i1 i2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz
    subst hx; subst hz; omega
  · intro x z x' z' hx hz i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz
    subst hx; subst hz; omega

end E195S68


namespace E195S73
open Erdos195 E195Tree

lemma pairwise_idx' {S : ℤ → ℤ → Prop} {P : List ℤ} (hP : P.Pairwise S) {x y : ℤ}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : P.idxOf x < P.idxOf y) : S x y := by
  have hxl := List.idxOf_lt_length_of_mem hx
  have hyl := List.idxOf_lt_length_of_mem hy
  have := List.pairwise_iff_getElem.1 hP _ _ hxl hyl hxy
  rwa [List.getElem_idxOf hxl, List.getElem_idxOf hyl] at this

theorem safe_of_pairwise_rev' {R : ℤ → ℤ → Prop} (hA : No3AP R) (hB : Star R)
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
  | exact hA' ⟨pairwise_idx' hP q1 p2 i12, pairwise_idx' hP p0 p1 i01⟩
  | exact hA1 ⟨r12, r23⟩
  | exact hasymm _ _ ((hB a r hr).2 r23) (pairwise_idx' hP p0 p1 i01)

end E195S73

namespace Erdos195
open E195Tree E195S73

/-- The reverse of a tree order is the tree order with all node bits negated. -/
theorem treeLt_flip_iff (θ : ℕ → ℤ → Bool) (x y : ℤ) :
    treeLt (fun k r => !θ k r) x y ↔ treeLt θ y x := by
  by_cases hne : x = y
  · subst hne; simp [treeLt]
  have dn := bit_ne hne
  have hm : x % 2 ^ padicValInt 2 (y - x) = y % 2 ^ padicValInt 2 (y - x) :=
    emod_eq_of_dvd (two_pow_val_dvd _)
  unfold treeLt
  rw [padicValInt_sub_comm x y, ← hm]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨Ne.symm hne, ?_⟩
    cases hθ : θ (padicValInt 2 (y - x)) (x % 2 ^ padicValInt 2 (y - x)) <;>
      simp_all
  · rintro ⟨-, h⟩
    refine ⟨hne, ?_⟩
    cases hθ : θ (padicValInt 2 (y - x)) (x % 2 ^ padicValInt 2 (y - x)) <;>
      simp_all

/-- **Tree reverse-order safety.** A word listed in increasing `≺_θ` order is SAFE for the
reversed tree order `≺_{¬θ}`. (Generalizes milestone #9 from ε-orders to tree orders.) -/
theorem treeLt_sorted_safe (θ : ℕ → ℤ → Bool) (L : List ℤ) (hL : L.Pairwise (treeLt θ)) :
    Safe (treeLt (fun k r => !θ k r)) L := by
  apply safe_of_pairwise_rev' (treeLt_no3AP _) (treeLt_star _)
  · intro x y h1 h2
    exact (treeLt_trans _ h1 h2).1 rfl
  · exact hL.imp (fun {a b} h => (treeLt_flip_iff θ b a).2 h)


/-- In the tree order with `θ k _ = ¬ bit_k z`, the integer `z` is the greatest element. -/
lemma treeLt_to_max (z x : ℤ) (hx : x ≠ z) :
    treeLt (fun k _ => !decide (z / 2 ^ k % 2 = 1)) x z := by
  refine ⟨hx, ?_⟩
  have dn := bit_ne hx
  unfold bitOne at dn ⊢
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  tauto

/-- **Specified-last-entry ordering.** Every finite set `X` of integers and every `z ∈ X`
have a duplicate-free ordering of `X` that ends at `z` and is SAFE for some tree order. -/
theorem specified_last_safe_order (X : Finset ℤ) (z : ℤ) (hz : z ∈ X) :
    ∃ L : List ℤ, L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ X) ∧ L.getLast? = some z ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L := by
  classical
  set θ0 : ℕ → ℤ → Bool := fun k _ => !decide (z / 2 ^ k % 2 = 1) with hθ0
  let r : ℤ → ℤ → Prop := fun x y => x = y ∨ treeLt θ0 x y
  haveI : IsTotal ℤ r := ⟨fun a b => by
    by_cases h : a = b
    · exact Or.inl (Or.inl h)
    · rcases treeLt_total θ0 h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inr h')⟩
  haveI : IsTrans ℤ r := ⟨fun a b c h1 h2 => by
    rcases h1 with rfl | h1
    · exact h2
    rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (treeLt_trans θ0 h1 h2)⟩
  let S := ((X.erase z).toList).insertionSort r
  have hperm : S.Perm (X.erase z).toList := List.perm_insertionSort r _
  have hSnd : S.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
  have hSmem : ∀ x, x ∈ S ↔ x ∈ X.erase z := fun x => by
    rw [hperm.mem_iff, Finset.mem_toList]
  have hSr : S.Pairwise r := List.pairwise_insertionSort r _
  have hSlt : S.Pairwise (treeLt θ0) := by
    have := hSr.and hSnd
    exact this.imp (fun {a b} h => by
      rcases h with ⟨rfl | h, hne⟩
      · exact absurd rfl hne
      · exact h)
  refine ⟨S ++ [z], ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hSnd, List.nodup_singleton z, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact (Finset.mem_erase.1 ((hSmem _).1 ha)).1 rfl
  · intro x
    simp only [List.mem_append, List.mem_singleton, hSmem, Finset.mem_erase]
    constructor
    · rintro (⟨-, h⟩ | rfl)
      · exact h
      · exact hz
    · intro hx
      by_cases h : x = z
      · exact Or.inr h
      · exact Or.inl ⟨h, hx⟩
  · simp
  · refine ⟨fun k r => !θ0 k r, treeLt_sorted_safe θ0 _ ?_⟩
    rw [List.pairwise_append]
    refine ⟨hSlt, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact treeLt_to_max _ a (Finset.mem_erase.1 ((hSmem _).1 ha)).1

end Erdos195


namespace E195S68
open Erdos195 E195Tree E195Par E195W

lemma idx_mem_lt {P S : List ℤ} {u : ℤ} (hu : u ∈ P) : (P ++ S).idxOf u < P.length := by
  rw [List.idxOf_append_of_mem hu]; exact List.idxOf_lt_length_of_mem hu

lemma idx_not_ge {P S : List ℤ} {u : ℤ} (hu : u ∉ P) : P.length ≤ (P ++ S).idxOf u := by
  rw [List.idxOf_append_of_notMem hu]; omega

lemma idx_not_gt {P S : List ℤ} {u v : ℤ} (hu : u ∉ P) (hv : u ≠ v) :
    P.length < (P ++ v :: S).idxOf u := by
  rw [List.idxOf_append_of_notMem hu, List.idxOf_cons_ne _ (Ne.symm hv)]; omega

lemma idx_eq_len {P S : List ℤ} {v : ℤ} (hv : v ∉ P) : (P ++ v :: S).idxOf v = P.length := by
  rw [List.idxOf_append_of_notMem hv]; simp

end E195S68

namespace E195S73
open Erdos195 E195Tree

lemma idx_lt_of_mem_not {T R : List ℤ} {u v : ℤ} (hu : u ∈ T) (hv : v ∉ T) :
    (T ++ R).idxOf u < (T ++ R).idxOf v := by
  rw [List.idxOf_append_of_mem hu, List.idxOf_append_of_notMem hv]
  have := List.idxOf_lt_length_of_mem hu
  omega

lemma idx_mem_mem {T R : List ℤ} {u v : ℤ} (hu : u ∈ T) (hv : v ∈ T) :
    (T ++ R).idxOf u < (T ++ R).idxOf v ↔ T.idxOf u < T.idxOf v := by
  rw [List.idxOf_append_of_mem hu, List.idxOf_append_of_mem hv]

lemma val_odd_zero {d : ℤ} (hd : d % 2 = 1) : padicValInt 2 d = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  omega

end E195S73

namespace Erdos195
open E195Tree E195S73

/-- **Interlocked pairs never close.** Let `(a,b)` and `(a',b')` be in-order pairs of a word `T`
whose third/fourth terms are swapped: `2b−a = 3b'−2a'` and `3b−2a = 2b'−a'`, and suppose neither
of these two values occurs in `T`. Then in every SAFE extension `T ++ R` (for any tree order),
neither value ever occurs, so both pairs stay open forever. -/
theorem interlocked_pairs_never_close (θ : ℕ → ℤ → Bool) (T R : List ℤ) (a b a' b' : ℤ)
    (ha : a ∈ T) (hb : b ∈ T) (ha' : a' ∈ T) (hb' : b' ∈ T)
    (hi : T.idxOf a < T.idxOf b) (hi' : T.idxOf a' < T.idxOf b')
    (ht : 2 * b - a = 3 * b' - 2 * a') (hw : 3 * b - 2 * a = 2 * b' - a')
    (htT : 2 * b - a ∉ T) (hwT : 3 * b - 2 * a ∉ T)
    (hS : Safe (treeLt θ) (T ++ R)) :
    2 * b - a ∉ T ++ R ∧ 3 * b - 2 * a ∉ T ++ R := by
  obtain ⟨h1, -⟩ := (treeLt_safe_iff θ (T ++ R)).1 hS
  have mT : ∀ x ∈ T, x ∈ T ++ R := fun x hx => List.mem_append_left _ hx
  have wclaim : 3 * b - 2 * a ∈ T ++ R →
      2 * b - a ∈ T ++ R ∧ (T ++ R).idxOf (2 * b - a) < (T ++ R).idxOf (3 * b - 2 * a) := by
    intro hwW
    have := h1 a' b' (mT _ ha') (mT _ hb') (by rw [← hw]; exact hwW)
      ((idx_mem_mem ha' hb').2 hi') (by rw [← hw]; exact idx_lt_of_mem_not hb' hwT)
    rw [← ht, ← hw] at this
    exact this
  constructor
  · intro htW
    obtain ⟨hwW, hlt⟩ := h1 a b (mT _ ha) (mT _ hb) htW ((idx_mem_mem ha hb).2 hi)
      (idx_lt_of_mem_not hb htT)
    have := (wclaim hwW).2
    omega
  · intro hwW
    obtain ⟨htW, hlt⟩ := wclaim hwW
    obtain ⟨-, hlt'⟩ := h1 a b (mT _ ha) (mT _ hb) htW ((idx_mem_mem ha hb).2 hi)
      (idx_lt_of_mem_not hb htT)
    omega

/-- **Interlocked root obstruction (excluded case of Astra's single-inversion repair lemma).**
If a word `T` contains an odd `b` before an even `c`, and `q = 5c−4b` before `p = 4c−3b`, while
neither `t = 2c−b` nor `w = 3c−2b` occurs in `T`, then NO extension `T ++ R` is SAFE for any
tree order: the pairs `(b,c)` and `(q,p)` stay open forever and demand opposite root bits. -/
theorem interlocked_root_obstruction (T R : List ℤ) (b c : ℤ)
    (hb : b ∈ T) (hc : c ∈ T) (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hp : 4 * c - 3 * b ∈ T) (hq : 5 * c - 4 * b ∈ T)
    (hbc : T.idxOf b < T.idxOf c) (hqp : T.idxOf (5 * c - 4 * b) < T.idxOf (4 * c - 3 * b))
    (htT : 2 * c - b ∉ T) (hwT : 3 * c - 2 * b ∉ T) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by
  rintro ⟨θ, hS⟩
  have e1 : 2 * c - b = 3 * (4 * c - 3 * b) - 2 * (5 * c - 4 * b) := by ring
  have e2 : 3 * c - 2 * b = 2 * (4 * c - 3 * b) - (5 * c - 4 * b) := by ring
  obtain ⟨ntW, nwW⟩ := interlocked_pairs_never_close θ T R b c _ _ hb hc hq hp hbc hqp e1 e2
    htT hwT hS
  obtain ⟨-, h2⟩ := (treeLt_safe_iff θ (T ++ R)).1 hS
  have mT : ∀ x ∈ T, x ∈ T ++ R := fun x hx => List.mem_append_left _ hx
  have c1 := h2 b c (mT _ hb) (mT _ hc) ((idx_mem_mem hb hc).2 hbc) ntW nwW
  have c2 := h2 _ _ (mT _ hq) (mT _ hp) ((idx_mem_mem hq hp).2 hqp) (by rw [← e2]; exact nwW)
    (by rw [← e1]; exact ntW)
  have v1 : padicValInt 2 (c - b) = 0 := val_odd_zero (by omega)
  have v2 : padicValInt 2 (4 * c - 3 * b - (5 * c - 4 * b)) = 0 := val_odd_zero (by omega)
  rw [v1] at c1
  rw [v2] at c2
  unfold bitOne at c1 c2
  simp only [pow_zero, Int.emod_one, Int.ediv_one] at c1 c2
  have : (4 * c - 3 * b) % 2 = 1 := by omega
  rw [this] at c2
  have : ¬ c % 2 = 1 := by omega
  simp_all

end Erdos195

namespace E195S75
open Erdos195 E195Tree E195Par E195W E195S68

set_option maxHeartbeats 4000000 in
/-- Core of the positive half of the single-inversion lemma. -/
theorem single_inversion_core (U V L M : List ℤ) (b c : ℤ)
    (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hU : ∀ x ∈ U, x % 4 = c % 4) (hV : ∀ x ∈ V, x % 4 = b % 4) (hcU : c ∉ U)
    (hE : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [c]))
    (hO : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([b] ++ V))
    (hLM : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (L ++ M))
    (hmem : ∀ u, u ∈ L ∨ u ∈ M ↔ ∃ v ∈ [b] ++ V, u = 2 * (3 * c - 2 * b) - v)
    (htL : 2 * c - b ∉ L)
    (hM : M = [] ∨ (M = [2 * c - b] ∧ 5 * c - 4 * b ∉ U ++ [c])) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ L ++ [3 * c - 2 * b] ++ M) := by
  classical
  have Mt : ∀ u ∈ M, u = 2 * c - b ∧ 5 * c - 4 * b ∉ U ++ [c] := by
    intro u hu
    rcases hM with h | ⟨h, hq⟩
    · simp [h] at hu
    · simp [h] at hu; exact ⟨hu, hq⟩
  generalize hw : 3 * c - 2 * b = w at hmem ⊢
  have rLM : ∀ u, u ∈ L ∨ u ∈ M → u % 4 = (b + 2) % 4 ∧ 2 * w - u ∈ [b] ++ V := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := (hmem u).1 hu
    have hv4 : v % 4 = b % 4 := by
      simp only [List.mem_append, List.mem_singleton] at hv
      rcases hv with h | h
      · rw [h]
      · exact hV v h
    refine ⟨by omega, ?_⟩
    rw [show 2 * w - (2 * w - v) = v by ring]; exact hv
  have refl : ∀ v ∈ [b] ++ V, 2 * w - v ∈ L ∨ 2 * w - v ∈ M := fun v hv => (hmem _).2 ⟨v, hv, rfl⟩
  have oV : ∀ u ∈ V, u % 2 = 1 := fun u hu => by have := hV u hu; omega
  have eU : ∀ u ∈ U, u % 2 = 0 := fun u hu => by have := hU u hu; omega
  have oL : ∀ u ∈ L, u % 2 = 1 := fun u hu => by have := (rLM u (Or.inl hu)).1; omega
  have oM : ∀ u ∈ M, u % 2 = 1 := fun u hu => by have := (rLM u (Or.inr hu)).1; omega
  have w4 : w % 4 = (c + 2) % 4 := by omega
  have p2 : (2 : ℤ) ^ (0 + 1) = 2 := by norm_num
  have p4 : (2 : ℤ) ^ (1 + 1) = 4 := by norm_num
  have mPre : ∀ u, u ∈ U ++ [b, c] ++ V ++ L ↔ u ∈ U ∨ u = b ∨ u = c ∨ u ∈ V ∨ u ∈ L := by
    intro u; simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false]; tauto
  have wnot : w ∉ U ++ [b, c] ++ V ++ L := by
    rw [mPre]
    rintro (h | h | h | h | h)
    · have := hU w h; omega
    · omega
    · omega
    · have := oV w h; omega
    · have := oL w h; omega
  have Mnot : ∀ u ∈ M, u ∉ U ++ [b, c] ++ V ++ L ∧ u ≠ w := by
    intro u hu
    have hu4 := (rLM u (Or.inr hu)).1
    have hut := (Mt u hu).1
    refine ⟨?_, fun e => by have := oM u hu; omega⟩
    rw [mPre]
    rintro (h | h | h | h | h)
    · have := hU u h; omega
    · omega
    · omega
    · have := hV u h; omega
    · exact htL (hut ▸ h)
  have eW : U ++ [b, c] ++ V ++ L ++ [w] ++ M = (U ++ [b, c] ++ V ++ L) ++ w :: M := by simp
  rw [eW]
  generalize hW : (U ++ [b, c] ++ V ++ L) ++ w :: M = W
  have mW : ∀ u, u ∈ W ↔ u ∈ U ∨ u = b ∨ u = c ∨ u ∈ V ∨ u ∈ L ∨ u = w ∨ u ∈ M := by
    intro u; rw [← hW, List.mem_append, mPre, List.mem_cons]; tauto
  have preW : ∀ u ∈ U ++ [b, c] ++ V ++ L, u ∈ W := by
    intro u hu; rw [← hW]; exact List.mem_append_left _ hu
  have wW : w ∈ W := by rw [← hW]; simp
  -- index facts
  have iw : W.idxOf w = (U ++ [b, c] ++ V ++ L).length := by rw [← hW]; exact idx_eq_len wnot
  have iP : ∀ u ∈ U ++ [b, c] ++ V ++ L, W.idxOf u < (U ++ [b, c] ++ V ++ L).length := by
    intro u hu; rw [← hW]; exact idx_mem_lt hu
  have iP' : ∀ u, u ∉ U ++ [b, c] ++ V ++ L → u ≠ w → (U ++ [b, c] ++ V ++ L).length < W.idxOf u := by
    intro u hu hne; rw [← hW]; exact idx_not_gt hu hne
  have eU1 : W = U ++ (b :: c :: (V ++ L ++ w :: M)) := by rw [← hW]; simp
  have eU2 : W = (U ++ [b]) ++ c :: (V ++ L ++ w :: M) := by rw [← hW]; simp
  have bU : b ∉ U := fun h => by have := eU b h; omega
  have cUb : c ∉ U ++ [b] := by
    simp only [List.mem_append, List.mem_singleton]; rintro (h | h)
    · exact hcU h
    · omega
  have iU : ∀ u ∈ U, W.idxOf u < U.length := by intro u hu; rw [eU1]; exact idx_mem_lt hu
  have iU' : ∀ u, u ∉ U → U.length ≤ W.idxOf u := by intro u hu; rw [eU1]; exact idx_not_ge hu
  have ib : W.idxOf b = U.length := by rw [eU1]; exact idx_eq_len bU
  have ic : W.idxOf c = U.length + 1 := by
    rw [eU2, idx_eq_len cUb]; simp
  have iC' : ∀ u, u ∉ U ++ [b] → U.length + 1 ≤ W.idxOf u := by
    intro u hu; have := idx_not_ge (S := c :: (V ++ L ++ w :: M)) hu; rw [← eU2] at this
    simpa using this
  generalize (U ++ [b, c] ++ V ++ L).length = nP at iw iP iP'
  generalize U.length = nU at iU iU' ib ic iC'
  have oddW : ∀ u ∈ W, u % 2 = 1 → u = b ∨ u ∈ V ∨ u ∈ L ∨ u ∈ M := by
    intro u hu ho
    rcases (mW u).1 hu with h | h | h | h | h | h | h
    · have := eU u h; omega
    · exact Or.inl h
    · omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · omega
    · exact Or.inr (Or.inr (Or.inr h))
  have evenW : ∀ u ∈ W, u % 2 = 0 → u ∈ U ∨ u = c ∨ u = w := by
    intro u hu he
    rcases (mW u).1 hu with h | h | h | h | h | h | h
    · exact Or.inl h
    · omega
    · exact Or.inr (Or.inl h)
    · have := oV u h; omega
    · have := oL u h; omega
    · exact Or.inr (Or.inr h)
    · have := oM u h; omega
  -- an odd letter before c is b
  have beforeC : ∀ u ∈ W, u % 2 = 1 → W.idxOf u < W.idxOf c → u = b := by
    intro u hu ho i
    by_contra hne
    have : u ∉ U ++ [b] := by
      simp only [List.mem_append, List.mem_singleton]; rintro (h | h)
      · have := eU u h; omega
      · exact hne h
    have := iC' u this; omega
  have beforeB : ∀ u ∈ W, W.idxOf u < W.idxOf b → u ∈ U := by
    intro u hu i; by_contra h; have := iU' u h; omega
  have bV : ∀ v ∈ [b] ++ V, v ∈ U ++ [b, c] ++ V ++ L := by
    intro v hv; rw [mPre]
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have LM_W : ∀ u, u ∈ L ∨ u ∈ M → u ∈ W := by
    intro u hu; rcases hu with h | h
    · exact (mW u).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact (mW u).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  have LPre : ∀ u ∈ L, u ∈ U ++ [b, c] ++ V ++ L := fun u hu => by rw [mPre]; tauto
  have fz : ∀ L : List ℤ, (∀ u ∈ L, u % 2 = 1) → L.filter (fun x => decide (x % 2 = 0)) = [] :=
    fun L h => List.filter_eq_nil_iff.2 (fun u hu e => by have := h u hu; simp at e; omega)
  have fo : ∀ L : List ℤ, (∀ u ∈ L, u % 2 = 1) → L.filter (fun x => decide (x % 2 = 1)) = L :=
    fun L h => List.filter_eq_self.2 (fun u hu => by simp [h u hu])
  have fUe : U.filter (fun x => decide (x % 2 = 0)) = U :=
    List.filter_eq_self.2 (fun u hu => by simp [eU u hu])
  have fUo : U.filter (fun x => decide (x % 2 = 1)) = [] :=
    List.filter_eq_nil_iff.2 (fun u hu e => by have := eU u hu; simp at e; omega)
  have hb0 : ¬ b % 2 = 0 := by omega
  have hc1 : ¬ c % 2 = 1 := by omega
  have hw0 : w % 2 = 0 := by omega
  have hw1 : ¬ w % 2 = 1 := by omega
  apply two_child 0 W 0 0 1
  · intro x _; simp
  · intro x _; rw [p2]; omega
  · rw [← hW, p2]
    simp only [List.filter_append, List.filter_cons, List.filter_nil, fz V oV, fz L oL, fz M oM, fUe]
    simp only [hb0, hce, hw0, decide_false, decide_true, Bool.false_eq_true, if_false, if_true,
      List.nil_append, List.append_nil]
    apply block_sep 1 _ _ 0 (c % 4) ((c + 2) % 4) (by omega)
    · intro x hx; rw [pow_one]
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | h) | h
      · have := eU x h; omega
      · omega
      · omega
    · intro x hx; rw [p4]
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with h | h
      · exact hU x h
      · rw [h]
    · intro x hx; rw [p4]; simp at hx; omega
    · exact hE
    · exact single_safe w
  · rw [← hW, p2]
    simp only [List.filter_append, List.filter_cons, List.filter_nil, fo V oV, fo L oL, fo M oM, fUo]
    simp only [hbo, hc1, hw1, decide_false, decide_true, Bool.false_eq_true, if_false, if_true,
      List.nil_append, List.append_nil]
    rw [show [b] ++ V ++ L ++ M = ([b] ++ V) ++ (L ++ M) by simp]
    apply block_sep 1 _ _ 1 (b % 4) ((b + 2) % 4) (by omega)
    · intro x hx; rw [pow_one]
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | h) | (h | h)
      · omega
      · have := oV x h; omega
      · have := oL x h; omega
      · have := oM x h; omega
    · intro x hx; rw [p4]
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]
      · exact hV x h
    · intro x hx; rw [p4]
      simp only [List.mem_append] at hx
      exact (rLM x hx).1
    · exact hO
    · exact hLM
  · intro x z hx hz hs h2 i1 i2
    rw [p2] at hs
    by_cases hx0 : x % 2 = 0
    · have hz1 : z % 2 = 1 := by omega
      rcases evenW _ h2 (by omega) with h | h | h
      · exfalso
        have := iU _ h
        have := iU' z (fun hzU => by have := eU z hzU; omega)
        omega
      · exfalso
        have zb := beforeC z hz hz1 (by rw [← h]; exact i2)
        rw [zb] at i1
        have xU := beforeB x hx i1
        have := hU x xU
        omega
      · -- 2z - x = w
        have xE : x ∈ U ∨ x = c := by
          rcases evenW x hx hx0 with h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
          · exfalso; rw [h'] at i1; rw [h] at i2; omega
        have e3 : 3 * z - 2 * x = 2 * w - z := by omega
        rw [e3, h, iw]
        rcases oddW z hz hz1 with hzb | hzV | hzL | hzM
        · rcases refl z (by simp [hzb]) with h' | h'
          · exact ⟨preW _ (LPre _ h'), iP _ (LPre _ h')⟩
          · exfalso
            obtain ⟨et, hq⟩ := Mt _ h'
            apply hq
            simp only [List.mem_append, List.mem_singleton]
            rw [show 5 * c - 4 * b = x by omega]; exact xE
        · rcases refl z (by simp [hzV]) with h' | h'
          · exact ⟨preW _ (LPre _ h'), iP _ (LPre _ h')⟩
          · exfalso
            obtain ⟨et, hq⟩ := Mt _ h'
            apply hq
            simp only [List.mem_append, List.mem_singleton]
            rw [show 5 * c - 4 * b = x by omega]; exact xE
        · have := (rLM z (Or.inl hzL)).2
          exact ⟨preW _ (bV _ this), iP _ (bV _ this)⟩
        · exfalso
          obtain ⟨n1, n2⟩ := Mnot z hzM
          have := iP' z n1 n2
          rw [h, iw] at i2; omega
    · have hx1 : x % 2 = 1 := by omega
      have hz0 : z % 2 = 0 := by omega
      rcases evenW z hz hz0 with h | h | h
      · exfalso
        have := iU _ h
        have := iU' x (fun hxU => by have := eU x hxU; omega)
        omega
      · rw [h] at i1 i2 ⊢
        have xb := beforeC x hx hx1 i1
        rw [xb] at i2 ⊢
        have tW := h2
        rw [h, xb] at tW
        have tnP : 2 * c - b ∉ U ++ [b, c] ++ V ++ L := by
          rw [mPre]
          rintro (h' | h' | h' | h' | h')
          · have := eU _ h'; omega
          · omega
          · omega
          · have := hV _ h'; omega
          · exact htL h'
        have := iP' _ tnP (by omega)
        rw [show 3 * c - 2 * b = w by omega, iw]
        exact ⟨wW, this⟩
      · rw [h] at i1 i2 h2 ⊢
        rw [iw] at i2
        have ny : 2 * w - x ∉ U ++ [b, c] ++ V ++ L := fun hm => by have := iP _ hm; omega
        have nyw : 2 * w - x ≠ w := fun e => by omega
        have yM : 2 * w - x ∈ M := by
          rcases (mW _).1 h2 with h' | h' | h' | h' | h' | h' | h'
          · exact absurd (by rw [mPre]; exact Or.inl h') ny
          · exact absurd (by rw [mPre]; exact Or.inr (Or.inl h')) ny
          · exact absurd (by rw [mPre]; exact Or.inr (Or.inr (Or.inl h'))) ny
          · exact absurd (by rw [mPre]; exact Or.inr (Or.inr (Or.inr (Or.inl h')))) ny
          · exact absurd (by rw [mPre]; exact Or.inr (Or.inr (Or.inr (Or.inr h')))) ny
          · exact absurd h' nyw
          · exact h'
        have et := (Mt _ yM).1
        have cP : c ∈ U ++ [b, c] ++ V ++ L := by rw [mPre]; exact Or.inr (Or.inr (Or.inl rfl))
        rw [show 3 * w - 2 * x = c by omega]
        refine ⟨preW _ cP, ?_⟩
        have := iP _ cP
        have := iP' _ ny nyw
        omega
  · have openO : ∀ x z, x ∈ W → z ∈ W → W.idxOf x < W.idxOf z → 2 * z - x ∉ W →
        3 * z - 2 * x ∉ W → x % 2 ^ (0 + 1) ≠ z % 2 ^ (0 + 1) → z % 2 = 1 := by
      intro x z hx hz i n2 n3 hs
      rw [p2] at hs
      by_contra hz1
      have hx1 : x % 2 = 1 := by omega
      rcases evenW z hz (by omega) with h | h | h
      · have := iU _ h
        have := iU' x (fun hxU => by have := eU x hxU; omega)
        omega
      · rw [h] at i n3
        have xb := beforeC x hx hx1 i
        rw [xb, hw] at n3
        exact n3 wW
      · rw [h] at i n2
        have xP : x ∈ U ++ [b, c] ++ V ++ L := by
          by_contra hm
          have := iP' x hm (fun e => by omega)
          omega
        rcases oddW x hx hx1 with hb' | hV' | hL' | hM'
        · exact n2 (LM_W _ (refl x (by simp [hb'])))
        · exact n2 (LM_W _ (refl x (by simp [hV'])))
        · exact n2 (preW _ (bV _ (rLM x (Or.inl hL')).2))
        · exact (Mnot x hM').1 xP
    intro x z x' z' hx hz i n2 n3 hs hx' hz' i' n2' n3' hs'
    have e1 := openO x z hx hz i n2 n3 hs
    have e2 := openO x' z' hx' hz' i' n2' n3' hs'
    unfold bitOne; simp only [pow_zero, Int.ediv_one]; omega

end E195S75

namespace E195S75
open Erdos195 E195Tree E195Par E195W E195S68

lemma nodup_ext (U V R : List ℤ) (b c : ℤ) (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hU : ∀ x ∈ U, x % 4 = c % 4) (hV : ∀ x ∈ V, x % 4 = b % 4)
    (hnd : (U ++ [b, c] ++ V).Nodup) (hR : R.Nodup)
    (hcl : ∀ u ∈ R, u % 4 = (b + 2) % 4 ∨ u % 4 = (c + 2) % 4) :
    (U ++ [b, c] ++ V ++ R).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnd, hR, ?_⟩
  intro x hx u hu e
  subst e
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hcl x hu with h | h
  · rcases hx with ((h' | h' | h') | h')
    · have := hU x h'; omega
    · omega
    · omega
    · have := hV x h'; omega
  · rcases hx with ((h' | h' | h') | h')
    · have := hU x h'; omega
    · omega
    · omega
    · have := hV x h'; omega

end E195S75

namespace Erdos195
open E195Tree E195Par E195W E195S68 E195S75

set_option maxHeartbeats 4000000 in
/-- **Astra's single-inversion lemma (I), as an exact criterion.**
Let `T = U·(b,c)·V` with `b` odd, `c` even, all entries of `E = U·c` in the class of `c` mod 4,
all entries of `O = b·V` in the class of `b` mod 4, `T` duplicate-free, and `E`, `O` SAFE.
Put `p = 4c−3b`, `q = 5c−4b`. Then `T` has a SAFE end-extension `T ++ R` iff `p ∉ O ∨ q ∉ E`.
Moreover, when this holds, an extension with exactly `|O|+1 = |V|+2` new, distinct entries exists. -/
theorem single_inversion_iff (U V : List ℤ) (b c : ℤ)
    (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hU : ∀ x ∈ U, x % 4 = c % 4) (hV : ∀ x ∈ V, x % 4 = b % 4)
    (hnd : (U ++ [b, c] ++ V).Nodup)
    (hE : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [c]))
    (hO : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([b] ++ V)) :
    ((∃ R : List ℤ, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R)) ↔
      (4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c])) ∧
    ((4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c]) →
      ∃ R : List ℤ, R.length = V.length + 2 ∧ (U ++ [b, c] ++ V ++ R).Nodup ∧
        ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R)) := by
  classical
  have bU : b ∉ U := fun h => by have := hU b h; omega
  have cU : c ∉ U := by
    intro h
    have := (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 c h c (by simp) rfl
    exact this
  have cUb : c ∉ U ++ [b] := by
    simp only [List.mem_append, List.mem_singleton]; rintro (h | h)
    · exact cU h
    · omega
  have hOnd : ([b] ++ V).Nodup := by
    have h1 := List.nodup_append.1 hnd
    have h2 := List.nodup_append.1 h1.1
    rw [List.singleton_append, List.nodup_cons]
    refine ⟨fun h => h1.2.2 b (by simp) b h rfl, h1.2.1⟩
  have oO : ∀ v ∈ [b] ++ V, v % 4 = b % 4 := by
    intro v hv; simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with h | h
    · rw [h]
    · exact hV v h
  have strong : (4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c]) →
      ∃ R : List ℤ, R.length = V.length + 2 ∧ (U ++ [b, c] ++ V ++ R).Nodup ∧
        ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R) := by
    intro hI
    have finj : Function.Injective (fun x : ℤ => 2 * (3 * c - 2 * b) - x) := by
      intro x y e; simp only at e; omega
    have mapnd : (([b] ++ V).map (fun x => 2 * (3 * c - 2 * b) - x)).Nodup := hOnd.map finj
    by_cases hp : 4 * c - 3 * b ∈ [b] ++ V
    · -- delayed-t case: q ∉ E
      have hq : 5 * c - 4 * b ∉ U ++ [c] := by
        rcases hI with h | h
        · exact absurd hp h
        · exact h
      have htX : 2 * c - b ∈ (([b] ++ V).map (fun x => 2 * (3 * c - 2 * b) - x)).toFinset := by
        rw [List.mem_toFinset]
        exact List.mem_map.2 ⟨_, hp, by ring⟩
      obtain ⟨L1, hnd1, hmem1, hlast, hsafe⟩ := specified_last_safe_order _ _ htX
      obtain ⟨L, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
      have hLnd : L.Nodup := (List.nodup_append.1 hnd1).1
      have htL : 2 * c - b ∉ L := fun h =>
        (List.nodup_append.1 hnd1).2.2 _ h _ (List.mem_singleton_self _) rfl
      have hmem : ∀ u, u ∈ L ∨ u ∈ [2 * c - b] ↔ ∃ v ∈ [b] ++ V, u = 2 * (3 * c - 2 * b) - v := by
        intro u
        have := hmem1 u
        rw [List.mem_toFinset, List.mem_append, List.mem_map] at this
        rw [this]
        constructor
        · rintro ⟨v, hv, e⟩; exact ⟨v, hv, e.symm⟩
        · rintro ⟨v, hv, e⟩; exact ⟨v, hv, e.symm⟩
      obtain ⟨θ, hS⟩ := single_inversion_core U V L [2 * c - b] b c hbo hce hU hV cU hE hO hsafe
        hmem htL (Or.inr ⟨rfl, hq⟩)
      refine ⟨L ++ [3 * c - 2 * b, 2 * c - b], ?_, ?_, θ, by simpa using hS⟩
      · have e1 : (L ++ [2 * c - b]).length =
            (([b] ++ V).map (fun x => 2 * (3 * c - 2 * b) - x)).toFinset.card := by
          rw [← List.toFinset_card_of_nodup hnd1]
          congr 1
          ext u; rw [List.mem_toFinset, ← hmem1 u]
        rw [List.toFinset_card_of_nodup mapnd] at e1
        simp at e1 ⊢; omega
      · apply nodup_ext U V _ b c hbo hce hU hV hnd
        · rw [List.nodup_append]
          refine ⟨hLnd, ?_, ?_⟩
          · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
              List.nodup_nil, and_true]; omega
          · intro x hx u hu e
            subst e
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
            rcases hu with h | h
            · have := (hmem x).1 (Or.inl hx)
              obtain ⟨v, hv, ev⟩ := this
              have := oO v hv; omega
            · exact htL (h ▸ hx)
        · intro u hu
          simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hu
          rcases hu with h | h | h
          · obtain ⟨v, hv, ev⟩ := (hmem u).1 (Or.inl h)
            have := oO v hv; left; omega
          · right; omega
          · left; omega
    · -- p ∉ O: reflect O in its inherited order, then w
      set L := ([b] ++ V).map (fun x => 2 * (3 * c - 2 * b) - x) with hL
      have hsafe : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (L ++ []) := by
        obtain ⟨θ, hθ⟩ := hO
        obtain ⟨θ', h'⟩ := (safe_odd_affine_iff θ (-1) (2 * (3 * c - 2 * b)) (by norm_num)).1
        refine ⟨θ', ?_⟩
        have := (((safe_odd_affine_iff θ (-1) (2 * (3 * c - 2 * b)) (by norm_num)).2 θ' h').2 _).1 hθ
        rw [List.append_nil, hL]
        rwa [List.map_congr_left (fun x _ => by ring : ∀ x ∈ [b] ++ V,
          -1 * x + 2 * (3 * c - 2 * b) = 2 * (3 * c - 2 * b) - x)] at this
      have hmem : ∀ u, u ∈ L ∨ u ∈ ([] : List ℤ) ↔ ∃ v ∈ [b] ++ V, u = 2 * (3 * c - 2 * b) - v := by
        intro u
        rw [hL, List.mem_map]
        simp only [List.not_mem_nil, or_false]
        constructor
        · rintro ⟨v, hv, e⟩; exact ⟨v, hv, e.symm⟩
        · rintro ⟨v, hv, e⟩; exact ⟨v, hv, e.symm⟩
      have htL : 2 * c - b ∉ L := by
        intro h
        obtain ⟨v, hv, ev⟩ := (hmem _).1 (Or.inl h)
        apply hp
        rw [show 4 * c - 3 * b = v by omega]; exact hv
      obtain ⟨θ, hS⟩ := single_inversion_core U V L [] b c hbo hce hU hV cU hE hO hsafe
        hmem htL (Or.inl rfl)
      refine ⟨L ++ [3 * c - 2 * b], ?_, ?_, θ, by simpa using hS⟩
      · simp [hL]
      · apply nodup_ext U V _ b c hbo hce hU hV hnd
        · rw [List.nodup_append]
          refine ⟨mapnd, List.nodup_singleton _, ?_⟩
          intro x hx u hu e
          subst e
          simp only [List.mem_singleton] at hu
          obtain ⟨v, hv, ev⟩ := (hmem x).1 (Or.inl hx)
          have := oO v hv; omega
        · intro u hu
          simp only [List.mem_append, List.mem_singleton] at hu
          rcases hu with h | h
          · obtain ⟨v, hv, ev⟩ := (hmem u).1 (Or.inl h)
            have := oO v hv; left; omega
          · right; omega
  refine ⟨⟨?_, fun h => ?_⟩, strong⟩
  · rintro ⟨R, θ, hS⟩
    by_contra hneg
    push_neg at hneg
    obtain ⟨hp, hq⟩ := hneg
    have qU : 5 * c - 4 * b ∈ U := by
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with h | h
      · exact h
      · omega
    have pV : 4 * c - 3 * b ∉ U := fun h => by have := hU _ h; omega
    have eT1 : U ++ [b, c] ++ V = U ++ b :: c :: V := by simp
    have eT2 : U ++ [b, c] ++ V = (U ++ [b]) ++ c :: V := by simp
    apply interlocked_root_obstruction (U ++ [b, c] ++ V) R b c (by simp) (by simp) hbo hce
      (by
        simp only [List.mem_append, List.mem_singleton] at hp
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        tauto)
      (by simp [qU])
      (by
        rw [eT1, idx_eq_len bU]
        have := idx_eq_len (S := V) cUb
        rw [← eT2, eT1] at this; rw [this]; simp)
      (by
        rw [eT1]
        have h1 := idx_mem_lt (S := b :: c :: V) qU
        have h2 := idx_not_ge (S := b :: c :: V) pV
        omega)
      (by
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        rintro ((h | h | h) | h)
        · have := hU _ h; omega
        · omega
        · omega
        · have := hV _ h; omega)
      (by
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        rintro ((h | h | h) | h)
        · have := hU _ h; omega
        · omega
        · omega
        · have := hV _ h; omega)
    exact ⟨θ, hS⟩
  · obtain ⟨R, -, -, hS⟩ := strong h
    exact ⟨R, hS⟩

end Erdos195



open Erdos195 in
theorem solution (U V : List ℤ) (b c : ℤ)
    (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hU : ∀ x ∈ U, x % 4 = c % 4) (hV : ∀ x ∈ V, x % 4 = b % 4)
    (hnd : (U ++ [b, c] ++ V).Nodup)
    (hE : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [c]))
    (hO : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([b] ++ V)) :
    ((∃ R : List ℤ, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R)) ↔
      (4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c])) ∧
    ((4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c]) →
      ∃ R : List ℤ, R.length = V.length + 2 ∧ (U ++ [b, c] ++ V ++ R).Nodup ∧
        ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R)) :=
  Erdos195.single_inversion_iff U V b c hbo hce hU hV hnd hE hO

#print axioms solution
