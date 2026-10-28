-- Prove2me | solution 1 for Erdos195.open_cycle_node_conflict
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T21:52:10.150751+00:00
-- url     : https://prove2.me/submissions/4e160d5d-be15-4766-8de5-cda0a66688ec

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

namespace E195S77
open Erdos195 E195Tree

/-- A pair `a` before `b` whose tree bit is "wrong" must be closed: either `2b−a` comes before `b`,
or `3b−2a` occurs (and precedes `2b−a` if that occurs). -/
lemma forced_pair (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q) (a b : ℤ)
    (ha : a ∈ Q) (hb : b ∈ Q) (hi : Q.idxOf a < Q.idxOf b)
    (hbad : ¬ (θ (padicValInt 2 (b - a)) (a % 2 ^ padicValInt 2 (b - a)) = true ↔
      bitOne b (padicValInt 2 (b - a)))) :
    (2 * b - a ∈ Q ∧ Q.idxOf (2 * b - a) < Q.idxOf b) ∨
      (3 * b - 2 * a ∈ Q ∧ (2 * b - a ∈ Q → Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a))) := by
  obtain ⟨h1, h2⟩ := (treeLt_safe_iff θ Q).1 hS
  have hab : a ≠ b := ne_of_idx hi
  by_cases ht : 2 * b - a ∈ Q
  · rcases lt_or_gt_of_ne (idx_ne ht (show 2 * b - a ≠ b by intro h; apply hab; omega)) with h | h
    · exact Or.inl ⟨ht, h⟩
    · obtain ⟨h3, h4⟩ := h1 a b ha hb ht hi h
      exact Or.inr ⟨h3, fun _ => h4⟩
  · by_cases hw : 3 * b - 2 * a ∈ Q
    · exact Or.inr ⟨hw, fun h => absurd h ht⟩
    · exact absurd (h2 a b ha hb hi ht hw) hbad

/-- Root specialization: with `θ(0,0)=1`, every odd letter followed by an even letter is a wrong pair. -/
lemma root_forced (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (Q : List ℤ) (hS : Safe (treeLt θ) Q)
    (a b : ℤ) (ha : a ∈ Q) (hb : b ∈ Q) (hao : a % 2 = 1) (hbe : b % 2 = 0)
    (hi : Q.idxOf a < Q.idxOf b) :
    (2 * b - a ∈ Q ∧ Q.idxOf (2 * b - a) < Q.idxOf b) ∨
      (3 * b - 2 * a ∈ Q ∧ (2 * b - a ∈ Q → Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a))) := by
  apply forced_pair θ Q hS a b ha hb hi
  have hv : padicValInt 2 (b - a) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    omega
  rw [hv]
  simp only [pow_zero, Int.emod_one, h00, true_iff, bitOne, Int.ediv_one]
  omega

lemma idx_left {T R : List ℤ} {x : ℤ} (hx : x ∈ T) : (T ++ R).idxOf x = T.idxOf x ∧ T.idxOf x < T.length :=
  ⟨List.idxOf_append_of_mem hx, List.idxOf_lt_length_of_mem hx⟩

lemma idx_right {T R : List ℤ} {x : ℤ} (hx : x ∉ T) : T.length ≤ (T ++ R).idxOf x := by
  rw [List.idxOf_append_of_notMem hx]; omega

end E195S77

namespace Erdos195
open E195Tree E195S77

/-- **w-forcing.** With root bit 1, if an odd `b` precedes an even `c` in `T` and neither `2c−b` nor
`3c−2b` lies in `T`, then every SAFE end-extension `T ++ R` contains `w = 3c−2b` in `R`, before
`t = 2c−b` if `t` occurs at all. -/
theorem w_forcing (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (T R : List ℤ)
    (hS : Safe (treeLt θ) (T ++ R)) (b c : ℤ) (hb : b ∈ T) (hc : c ∈ T)
    (hbo : b % 2 = 1) (hce : c % 2 = 0) (hi : T.idxOf b < T.idxOf c)
    (ht : 2 * c - b ∉ T) (hw : 3 * c - 2 * b ∉ T) :
    3 * c - 2 * b ∈ R ∧
      (2 * c - b ∈ R → (T ++ R).idxOf (3 * c - 2 * b) < (T ++ R).idxOf (2 * c - b)) := by
  have hbQ : b ∈ T ++ R := List.mem_append_left _ hb
  have hcQ : c ∈ T ++ R := List.mem_append_left _ hc
  have hiQ : (T ++ R).idxOf b < (T ++ R).idxOf c := by
    rw [(idx_left (R := R) hb).1, (idx_left (R := R) hc).1]; exact hi
  rcases root_forced θ h00 _ hS b c hbQ hcQ hbo hce hiQ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    have := idx_right (R := R) ht
    have := (idx_left (R := R) hc)
    omega
  · refine ⟨?_, fun htR => h2 (List.mem_append_right _ htR)⟩
    rcases List.mem_append.1 h1 with h | h
    · exact absurd h hw
    · exact h

/-- **Reflect-or-escape.** With root bit 1, every odd letter `o` before an even letter `w` is
reflected (`2w−o` occurs before `w`) or escapes (`3w−2o` occurs). -/
theorem reflect_or_escape (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (o w : ℤ) (ho : o ∈ Q) (hw : w ∈ Q) (hoo : o % 2 = 1)
    (hwe : w % 2 = 0) (hi : Q.idxOf o < Q.idxOf w) :
    (2 * w - o ∈ Q ∧ Q.idxOf (2 * w - o) < Q.idxOf w) ∨ 3 * w - 2 * o ∈ Q := by
  rcases root_forced θ h00 Q hS o w ho hw hoo hwe hi with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- **Two no-escape centres.** With root bit 1, let `u` precede `u'`, both even, such that no odd
letter before `u` (resp. `u'`) escapes at `u` (resp. `u'`). Then the odd letters before `u`,
translated by `δ = 2(u'−u)`, all occur before `u'`; and if some odd letter precedes `u`, then some
odd letter lies strictly between `u` and `u'`. -/
theorem no_escape_two_centres (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (u u' : ℤ) (hu : u ∈ Q) (hu' : u' ∈ Q) (hue : u % 2 = 0)
    (hue' : u' % 2 = 0) (hi : Q.idxOf u < Q.idxOf u')
    (hesc : ∀ o ∈ Q, o % 2 = 1 → (Q.idxOf o < Q.idxOf u → 3 * u - 2 * o ∉ Q) ∧
      (Q.idxOf o < Q.idxOf u' → 3 * u' - 2 * o ∉ Q)) :
    (∀ o ∈ Q, o % 2 = 1 → Q.idxOf o < Q.idxOf u →
      o + 2 * (u' - u) ∈ Q ∧ Q.idxOf (o + 2 * (u' - u)) < Q.idxOf u') ∧
    ((∃ o ∈ Q, o % 2 = 1 ∧ Q.idxOf o < Q.idxOf u) →
      ∃ o ∈ Q, o % 2 = 1 ∧ Q.idxOf u < Q.idxOf o ∧ Q.idxOf o < Q.idxOf u') := by
  -- reflection at a no-escape centre
  have refl : ∀ v, v ∈ Q → v % 2 = 0 → ∀ o ∈ Q, o % 2 = 1 → Q.idxOf o < Q.idxOf v →
      3 * v - 2 * o ∉ Q → 2 * v - o ∈ Q ∧ Q.idxOf (2 * v - o) < Q.idxOf v := by
    intro v hv hve o ho hoo hov hne
    rcases reflect_or_escape θ h00 Q hS o v ho hv hoo hve hov with h | h
    · exact h
    · exact absurd h hne
  have part1 : ∀ o ∈ Q, o % 2 = 1 → Q.idxOf o < Q.idxOf u →
      o + 2 * (u' - u) ∈ Q ∧ Q.idxOf (o + 2 * (u' - u)) < Q.idxOf u' := by
    intro o ho hoo hou
    obtain ⟨h1, h2⟩ := refl u hu hue o ho hoo hou ((hesc o ho hoo).1 hou)
    have h1o : (2 * u - o) % 2 = 1 := by omega
    have := refl u' hu' hue' (2 * u - o) h1 h1o (by omega)
      ((hesc _ h1 h1o).2 (by omega))
    have e : 2 * u' - (2 * u - o) = o + 2 * (u' - u) := by ring
    rw [e] at this; exact this
  refine ⟨part1, ?_⟩
  rintro ⟨o0, ho0, ho0o, ho0u⟩
  by_contra hno
  push Not at hno
  classical
  let s : Finset ℤ := (Q.filter (fun x => decide (x % 2 = 1 ∧ Q.idxOf x < Q.idxOf u))).toFinset
  have mem_s : ∀ x, x ∈ s ↔ x ∈ Q ∧ x % 2 = 1 ∧ Q.idxOf x < Q.idxOf u := by
    intro x; simp [s]
  have hne : s.Nonempty := ⟨o0, (mem_s o0).2 ⟨ho0, ho0o, ho0u⟩⟩
  set δ := 2 * (u' - u) with hδ
  obtain ⟨M, hM, hMmax⟩ := Finset.exists_max_image s (fun x => δ * x) hne
  obtain ⟨hMQ, hMo, hMu⟩ := (mem_s M).1 hM
  obtain ⟨hT1, hT2⟩ := part1 M hMQ hMo hMu
  have hTo : (M + δ) % 2 = 1 := by omega
  have hTu : Q.idxOf (M + δ) < Q.idxOf u := by
    rcases lt_trichotomy (Q.idxOf (M + δ)) (Q.idxOf u) with h | h | h
    · exact h
    · exfalso
      have : M + δ = u := by
        exact (List.idxOf_inj hT1).1 h
      omega
    · exact absurd hT2 (not_lt.2 (hno _ hT1 hTo h))
  have := hMmax (M + δ) ((mem_s _).2 ⟨hT1, hTo, hTu⟩)
  have hδ0 : δ ≠ 0 := by
    intro h0
    have : u' = u := by omega
    rw [this] at hi; exact lt_irrefl _ hi
  have : 0 < δ * δ := mul_self_pos.2 hδ0
  nlinarith

end Erdos195

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

namespace Erdos195
open E195Tree E195S73 E195S77

/-- **Interlocked obstruction at every level.** Let `a, a+d, a+4d, a+5d` (`d ≠ 0`) lie in a word
`T` with `a` before `a+d` and `a+5d` before `a+4d`, while the two middle terms `a+2d, a+3d` are
absent from `T`. Then no end-extension `T ++ R` is SAFE for any tree order. (The two pairs are
interlocked, hence never closed, and by `(*)` exactly one of them is increasing for any order
with `(*)`.) -/
theorem interlocked_obstruction (T R : List ℤ) (a d : ℤ) (hd : d ≠ 0)
    (h0 : a ∈ T) (h1 : a + d ∈ T) (h4 : a + 4 * d ∈ T) (h5 : a + 5 * d ∈ T)
    (hi : T.idxOf a < T.idxOf (a + d)) (hi' : T.idxOf (a + 5 * d) < T.idxOf (a + 4 * d))
    (h2 : a + 2 * d ∉ T) (h3 : a + 3 * d ∉ T) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by
  rintro ⟨θ, hS⟩
  have e1 : 2 * (a + d) - a = a + 2 * d := by ring
  have e2 : 3 * (a + d) - 2 * a = a + 3 * d := by ring
  have e3 : 3 * (a + 4 * d) - 2 * (a + 5 * d) = a + 2 * d := by ring
  have e4 : 2 * (a + 4 * d) - (a + 5 * d) = a + 3 * d := by ring
  obtain ⟨n2, n3⟩ := interlocked_pairs_never_close θ T R a (a + d) (a + 5 * d) (a + 4 * d)
    h0 h1 h5 h4 hi hi' (by rw [e1, e3]) (by rw [e2, e4]) (by rw [e1]; exact h2)
    (by rw [e2]; exact h3) hS
  rw [e1] at n2; rw [e2] at n3
  obtain ⟨-, hc⟩ := (treeLt_safe_iff θ (T ++ R)).1 hS
  have mT : ∀ x ∈ T, x ∈ T ++ R := fun x hx => List.mem_append_left _ hx
  have c1 := hc a (a + d) (mT _ h0) (mT _ h1) ((idx_mem_mem h0 h1).2 hi)
    (by rw [e1]; exact n2) (by rw [e2]; exact n3)
  have c2 := hc (a + 5 * d) (a + 4 * d) (mT _ h5) (mT _ h4) ((idx_mem_mem h5 h4).2 hi')
    (by rw [e4]; exact n3) (by rw [e3]; exact n2)
  have ne1 : a ≠ a + d := by intro h; apply hd; omega
  have ne2 : a + 5 * d ≠ a + 4 * d := by intro h; apply hd; omega
  have r1 : ¬ treeLt θ a (a + d) := (not_treeLt_iff θ ne1).2 c1
  have r2 : ¬ treeLt θ (a + 5 * d) (a + 4 * d) := (not_treeLt_iff θ ne2).2 c2
  have s1 := treeLt_star θ a d hd
  have s2 := treeLt_star θ (a + 5 * d) (-d) (by intro h; apply hd; omega)
  have q2 : a + 5 * d + -d = a + 4 * d := by ring
  have q3 : a + 5 * d + 2 * -d = a + 3 * d := by ring
  have q4 : a + 5 * d + 3 * -d = a + 2 * d := by ring
  rw [q2, q3, q4] at s2
  have ne3 : a + 2 * d ≠ a + 3 * d := by intro h; apply hd; omega
  rcases treeLt_total θ ne3 with h | h
  · exact r1 (s1.2 h)
  · exact r2 (s2.2 h)

/-- **Escape chains terminate.** With root bit 1, let an odd `o` precede an even `w` in a SAFE
word `Q`, and put `e m = o + 3^m (w − o)` (so `e 0 = w` and `e (m+1) = 3·e m − 2o` is the escape
of `o` at `e m`). Then for some `n`, all of `e 0, …, e n` occur in `Q`, `o` precedes
`e 0, …, e (n−1)`, and the chain stops at `e n` in one of two ways: `o` precedes `e n` and is
reflected there (`2·e n − o` occurs before `e n`), or `e n` occurs before `o` (then `n ≥ 1`). -/
theorem escape_chain_terminates (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (o w : ℤ) (ho : o ∈ Q) (hw : w ∈ Q) (hoo : o % 2 = 1)
    (hwe : w % 2 = 0) (hi : Q.idxOf o < Q.idxOf w) :
    ∃ n : ℕ, (∀ m ≤ n, o + 3 ^ m * (w - o) ∈ Q) ∧
      (∀ m < n, Q.idxOf o < Q.idxOf (o + 3 ^ m * (w - o))) ∧
      ((Q.idxOf o < Q.idxOf (o + 3 ^ n * (w - o)) ∧
          2 * (o + 3 ^ n * (w - o)) - o ∈ Q ∧
          Q.idxOf (2 * (o + 3 ^ n * (w - o)) - o) < Q.idxOf (o + 3 ^ n * (w - o))) ∨
        (0 < n ∧ Q.idxOf (o + 3 ^ n * (w - o)) < Q.idxOf o)) := by
  set e : ℕ → ℤ := fun m => o + 3 ^ m * (w - o) with he
  have hwo : w - o ≠ 0 := by intro h; omega
  have epar : ∀ m, e m % 2 = 0 := by
    intro m
    have h3 : Odd ((3 : ℤ) ^ m) := Odd.pow (by decide)
    have h4 : Odd (w - o) := by rw [Int.odd_iff]; omega
    have h5 : Odd ((3 : ℤ) ^ m * (w - o)) := h3.mul h4
    rw [Int.odd_iff] at h5
    simp only [he]; omega
  have ene : ∀ m, e m ≠ o := by
    intro m h; have := epar m; omega
  have e0 : e 0 = w := by simp [he]
  have esucc : ∀ m, e (m + 1) = 3 * e m - 2 * o := by intro m; simp only [he]; ring
  show ∃ n : ℕ, (∀ m ≤ n, e m ∈ Q) ∧ (∀ m < n, Q.idxOf o < Q.idxOf (e m)) ∧
    ((Q.idxOf o < Q.idxOf (e n) ∧ 2 * e n - o ∈ Q ∧ Q.idxOf (2 * e n - o) < Q.idxOf (e n)) ∨
      (0 < n ∧ Q.idxOf (e n) < Q.idxOf o))
  by_contra hno
  push Not at hno
  -- every stage of the chain is present and after `o`
  have key : ∀ n, (∀ m ≤ n, e m ∈ Q) ∧ (∀ m ≤ n, Q.idxOf o < Q.idxOf (e m)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun m hm => ?_, fun m hm => ?_⟩
      · rw [Nat.le_zero.1 hm, e0]; exact hw
      · rw [Nat.le_zero.1 hm, e0]; exact hi
    | succ n ih =>
      obtain ⟨A, B⟩ := ih
      have hn := hno n A (fun m hm => B m (by omega))
      have hen := A n le_rfl
      have hlt := B n le_rfl
      have nref := (hn.1 hlt)
      rcases reflect_or_escape θ h00 Q hS o (e n) ho hen hoo (epar n) hlt with h | h
      · have := nref h.1; have := h.2; omega
      · rw [← esucc] at h
        have A' : ∀ m ≤ n + 1, e m ∈ Q := by
          intro m hm
          rcases Nat.lt_or_ge m (n + 1) with h' | h'
          · exact A m (by omega)
          · rw [show m = n + 1 by omega]; exact h
        refine ⟨A', fun m hm => ?_⟩
        rcases Nat.lt_or_ge m (n + 1) with h' | h'
        · exact B m (by omega)
        · rw [show m = n + 1 by omega]
          have hn1 := (hno (n + 1) A' (fun m hm => B m (by omega))).2 (by omega)
          have hne := idx_ne ho (ene (n + 1)).symm
          omega
  have inj : Function.Injective e := by
    intro m k hmk
    simp only [he] at hmk
    have h1 : (3 : ℤ) ^ m * (w - o) = 3 ^ k * (w - o) := by linarith
    have h2 : (3 : ℤ) ^ m = 3 ^ k := mul_right_cancel₀ hwo h1
    exact Nat.pow_right_injective (show 2 ≤ 3 by norm_num) (by exact_mod_cast h2 : (3 : ℕ) ^ m = 3 ^ k)
  have hinf : ({x | x ∈ Q} : Set ℤ).Infinite :=
    Set.infinite_of_injective_forall_mem inj (fun m => (key m).1 m le_rfl)
  exact hinf (List.finite_toSet Q)

end Erdos195

namespace Erdos195
open E195Tree E195S73

/-- **Open cycles never close.** Let `(a i, b i)`, `i < m`, be in-order pairs of a word `T` whose
fourth term is the next pair's third term, cyclically: `3·b i − 2·a i = 2·b j − a j` with
`j = (i+1) % m`, and suppose no third term `2·b i − a i` lies in `T`. Then in every SAFE
extension `T ++ R` (any tree order) no third or fourth term of any of these pairs occurs, so all
of them stay open forever. (`m = 2` is the interlocked case.) -/
theorem open_cycle_never_closes (θ : ℕ → ℤ → Bool) (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (hS : Safe (treeLt θ) (T ++ R)) :
    ∀ i < m, 2 * b i - a i ∉ T ++ R ∧ 3 * b i - 2 * a i ∉ T ++ R := by
  obtain ⟨h1, -⟩ := (treeLt_safe_iff θ (T ++ R)).1 hS
  have mT : ∀ x ∈ T, x ∈ T ++ R := fun x hx => List.mem_append_left _ hx
  have hnext : ∀ i < m, (i + 1) % m < m := fun i hi' => Nat.mod_lt _ (by omega)
  have key : ∀ i < m, 2 * b i - a i ∉ T ++ R := by
    by_contra hc
    push Not at hc
    classical
    let s : Finset ℕ := (Finset.range m).filter (fun i => 2 * b i - a i ∈ T ++ R)
    have hne : s.Nonempty := by
      obtain ⟨i, him, hiQ⟩ := hc
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 him, hiQ⟩⟩
    obtain ⟨i, his, hmin⟩ := Finset.exists_min_image s
      (fun i => (T ++ R).idxOf (2 * b i - a i)) hne
    simp only [s, Finset.mem_filter, Finset.mem_range] at his
    obtain ⟨him, hiQ⟩ := his
    obtain ⟨hw, hlt⟩ := h1 (a i) (b i) (mT _ (ha i him)) (mT _ (hb i him)) hiQ
      ((idx_mem_mem (ha i him) (hb i him)).2 (hi i him))
      (idx_lt_of_mem_not (hb i him) (ht i him))
    rw [hcyc i him] at hw hlt
    have hj := hnext i him
    have := hmin ((i + 1) % m) (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hw⟩)
    omega
  intro i him
  refine ⟨key i him, ?_⟩
  rw [hcyc i him]
  exact key _ (hnext i him)

lemma prefix_chain_mono (P : ℕ → List ℤ) (hpre : ∀ n, P n <+: P (n + 1)) (N : ℕ) :
    ∀ k, P N <+: P (N + k) := by
  intro k
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (hpre (N + k))

/-- **Open cycles block exhaustive chains.** Let `P 0 ⊑ P 1 ⊑ …` be a prefix-increasing chain of
words, each SAFE for some tree order (the order may change from stage to stage), which covers
`ℤ`. Then no stage `P N` contains a cycle of in-order pairs `(a i, b i)`, `i < m`, `0 < m`,
with `3·b i − 2·a i = 2·b ((i+1)%m) − a ((i+1)%m)` and all third terms `2·b i − a i` absent
from `P N`. -/
theorem open_cycle_blocks_exhaustive_chain (P : ℕ → List ℤ) (hpre : ∀ n, P n <+: P (n + 1))
    (hsafe : ∀ n, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P n)) (hcov : ∀ x : ℤ, ∃ n, x ∈ P n)
    (N m : ℕ) (hm : 0 < m) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ P N) (hb : ∀ i < m, b i ∈ P N)
    (hi : ∀ i < m, (P N).idxOf (a i) < (P N).idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ P N) : False := by
  obtain ⟨n, hn⟩ := hcov (2 * b 0 - a 0)
  have hM : P n <+: P (N + n) := by
    have := prefix_chain_mono P hpre n N
    rw [Nat.add_comm] at this; exact this
  obtain ⟨R, hR⟩ := prefix_chain_mono P hpre N n
  obtain ⟨θ, hS⟩ := hsafe (N + n)
  rw [← hR] at hS
  have := (open_cycle_never_closes θ (P N) R m a b ha hb hi hcyc ht hS 0 hm).1
  apply this
  rw [hR]
  exact hM.subset hn

end Erdos195

namespace E195S80
open Erdos195 E195Tree

/-- Two integers congruent mod `2^k` with the same `k`-th digit are congruent mod `2^(k+1)`. -/
lemma dvd_succ_of_bit_iff {x y : ℤ} {k : ℕ} (h : (2 : ℤ) ^ k ∣ y - x)
    (hb : bitOne x k ↔ bitOne y k) : (2 : ℤ) ^ (k + 1) ∣ y - x := by
  unfold bitOne at hb
  have hm : x % 2 ^ k = y % 2 ^ k := emod_eq_of_dvd h
  have hp : (0 : ℤ) < 2 ^ k := by positivity
  have ex := Int.emod_add_mul_ediv x (2 ^ k)
  have ey := Int.emod_add_mul_ediv y (2 ^ k)
  have hq : (2 : ℤ) ∣ y / 2 ^ k - x / 2 ^ k := by omega
  obtain ⟨s, hs⟩ := hq
  refine ⟨s, ?_⟩
  have : y - x = 2 ^ k * (y / 2 ^ k - x / 2 ^ k) := by
    rw [mul_sub]; linarith
  rw [this, hs, pow_succ]; ring

end E195S80

namespace Erdos195
open E195Tree E195S73 E195S80

/-- **Open cycles force closures at their nodes, for every witness.** Let `(a i, b i)`, `i < m`,
be an open cycle in `T` (in-order pairs, `3·b i − 2·a i = 2·b (i+1 mod m) − a (i+1 mod m)`, no
third term `2·b i − a i` in `T`). Put `k = ν₂(b i − a i)`. In any SAFE extension `T ++ R`, for any
tree order, every in-order pair `(x, y)` at the same node (`ν₂(y − x) = k`, `x ≡ a i mod 2^k`)
whose second entry has the opposite `k`-th digit to `b i` (`y ≢ b i mod 2^(k+1)`) must be closed:
`2y − x` or `3y − 2x` occurs in `T ++ R`. -/
theorem open_cycle_forces_closure (θ : ℕ → ℤ → Bool) (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (hS : Safe (treeLt θ) (T ++ R))
    (i : ℕ) (him : i < m) (x y : ℤ) (hx : x ∈ T ++ R) (hy : y ∈ T ++ R)
    (hxy : (T ++ R).idxOf x < (T ++ R).idxOf y)
    (hk : padicValInt 2 (y - x) = padicValInt 2 (b i - a i))
    (hnode : (2 : ℤ) ^ padicValInt 2 (b i - a i) ∣ x - a i)
    (hbit : ¬ (2 : ℤ) ^ (padicValInt 2 (b i - a i) + 1) ∣ y - b i) :
    2 * y - x ∈ T ++ R ∨ 3 * y - 2 * x ∈ T ++ R := by
  by_contra hc
  push Not at hc
  obtain ⟨n2, n3⟩ := open_cycle_never_closes θ T R m a b ha hb hi hcyc ht hS i him
  obtain ⟨-, h2⟩ := (treeLt_safe_iff θ (T ++ R)).1 hS
  have mT : ∀ z ∈ T, z ∈ T ++ R := fun z hz => List.mem_append_left _ hz
  have c1 := h2 (a i) (b i) (mT _ (ha i him)) (mT _ (hb i him))
    ((idx_mem_mem (ha i him) (hb i him)).2 (hi i him)) n2 n3
  have c2 := h2 x y hx hy hxy hc.1 hc.2
  set k := padicValInt 2 (b i - a i) with hkdef
  rw [hk] at c2
  have hm : a i % 2 ^ k = x % 2 ^ k := emod_eq_of_dvd hnode
  rw [hm] at c1
  have hbits : bitOne (b i) k ↔ bitOne y k := c1.symm.trans c2
  have d1 : (2 : ℤ) ^ k ∣ b i - a i := two_pow_val_dvd _
  have d2 : (2 : ℤ) ^ k ∣ y - x := by rw [← hk]; exact two_pow_val_dvd _
  have d3 : (2 : ℤ) ^ k ∣ y - b i := by
    have : y - b i = (y - x) + (x - a i) - (b i - a i) := by ring
    rw [this]; exact dvd_sub (dvd_add d2 hnode) d1
  exact hbit (dvd_succ_of_bit_iff d3 hbits)

/-- **Open cycle with a node conflict kills every extension.** If two pairs `i, j` of an open cycle
in `T` lie at the same node (`ν₂(b j − a j) = ν₂(b i − a i) = k`, `a j ≡ a i mod 2^k`) but their
second entries have opposite `k`-th digits (`b j ≢ b i mod 2^(k+1)`), then no end-extension
`T ++ R` is SAFE for any tree order. (`m = 2`, pairs `(a, a+d)`, `(a+5d, a+4d)` is the interlocked
obstruction.) -/
theorem open_cycle_node_conflict (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (i j : ℕ) (him : i < m) (hjm : j < m)
    (hk : padicValInt 2 (b j - a j) = padicValInt 2 (b i - a i))
    (hnode : (2 : ℤ) ^ padicValInt 2 (b i - a i) ∣ a j - a i)
    (hbit : ¬ (2 : ℤ) ^ (padicValInt 2 (b i - a i) + 1) ∣ b j - b i) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by
  rintro ⟨θ, hS⟩
  have mT : ∀ z ∈ T, z ∈ T ++ R := fun z hz => List.mem_append_left _ hz
  obtain ⟨n2, n3⟩ := open_cycle_never_closes θ T R m a b ha hb hi hcyc ht hS j hjm
  rcases open_cycle_forces_closure θ T R m a b ha hb hi hcyc ht hS i him (a j) (b j)
    (mT _ (ha j hjm)) (mT _ (hb j hjm)) ((idx_mem_mem (ha j hjm) (hb j hjm)).2 (hi j hjm))
    hk hnode hbit with h | h
  · exact n2 h
  · exact n3 h

end Erdos195

namespace E195S80
open Erdos195 E195Tree

/-- Sanity: the interlocked obstruction (#141) is the case `m = 2` of the node-conflict theorem. -/
example (T R : List ℤ) (a d : ℤ) (hd : d ≠ 0)
    (h0 : a ∈ T) (h1 : a + d ∈ T) (h4 : a + 4 * d ∈ T) (h5 : a + 5 * d ∈ T)
    (hi : T.idxOf a < T.idxOf (a + d)) (hi' : T.idxOf (a + 5 * d) < T.idxOf (a + 4 * d))
    (h2 : a + 2 * d ∉ T) (h3 : a + 3 * d ∉ T) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by
  let A : ℕ → ℤ := fun i => if i = 0 then a else a + 5 * d
  let B : ℕ → ℤ := fun i => if i = 0 then a + d else a + 4 * d
  have hk : padicValInt 2 (B 1 - A 1) = padicValInt 2 (B 0 - A 0) := by
    simp only [A, B, if_pos, one_ne_zero, if_false]
    rw [padicValInt_sub_comm, show a + 5 * d - (a + 4 * d) = d by ring, show a + d - a = d by ring]
  apply open_cycle_node_conflict T R 2 A B
    (by intro i hi2; interval_cases i <;> simp [A, h0, h5])
    (by intro i hi2; interval_cases i <;> simp [B, h1, h4])
    (by intro i hi2; interval_cases i <;> simp [A, B, hi, hi'])
    (by intro i hi2; interval_cases i <;> simp [A, B] <;> ring)
    (by intro i hi2; interval_cases i <;> simp only [A, B] <;> norm_num
        · rw [show 2 * (a + d) - a = a + 2 * d by ring]; exact h2
        · rw [show 2 * (a + 4 * d) - (a + 5 * d) = a + 3 * d by ring]; exact h3)
    0 1 (by norm_num) (by norm_num) hk
  · simp only [A, B, if_pos, one_ne_zero, if_false]
    rw [show a + d - a = d by ring, show a + 5 * d - a = 5 * d by ring]
    exact (two_pow_val_dvd d).mul_left 5
  · simp only [A, B, if_pos, one_ne_zero, if_false]
    rw [show a + d - a = d by ring, show a + 4 * d - (a + d) = 3 * d by ring]
    intro h
    have h4 : (2 : ℤ) ^ (padicValInt 2 d + 1) ∣ 4 * d := by
      rw [pow_succ]
      exact (mul_dvd_mul (two_pow_val_dvd d) (dvd_refl 2)).trans ⟨2, by ring⟩
    have h1 : (2 : ℤ) ^ (padicValInt 2 d + 1) ∣ d := by
      have := dvd_sub h4 h; rwa [show 4 * d - 3 * d = d by ring] at this
    have := le_val_of_dvd hd h1
    omega

end E195S80


open Erdos195 in
theorem solution (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (i j : ℕ) (him : i < m) (hjm : j < m)
    (hk : padicValInt 2 (b j - a j) = padicValInt 2 (b i - a i))
    (hnode : (2 : ℤ) ^ padicValInt 2 (b i - a i) ∣ a j - a i)
    (hbit : ¬ (2 : ℤ) ^ (padicValInt 2 (b i - a i) + 1) ∣ b j - b i) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) :=
  Erdos195.open_cycle_node_conflict T R m a b ha hb hi hcyc ht i j him hjm hk hnode hbit

#print axioms solution
