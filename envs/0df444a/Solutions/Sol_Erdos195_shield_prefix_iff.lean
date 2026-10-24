-- Prove2me | solution 1 for Erdos195.shield_prefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:32:14.589286+00:00
-- url     : https://prove2.me/submissions/ce6f1567-d5fc-425a-9b0c-466ffa22783a

import Mathlib
import Definitions.Def_Erdos195_tree


namespace E94
open Erdos195

lemma val_add (a r : ℤ) : (a + r) - a = r := by ring
lemma val_add2 (a r : ℤ) : (a + 2 * r) - (a + r) = r := by ring
lemma val_add3 (a r : ℤ) : (a + 3 * r) - (a + 2 * r) = r := by ring

/-- with `k = ν₂ r`, adding `r` flips bit `k` and keeps the residue mod `2^k`. -/
lemma flip (a r : ℤ) (hr : r ≠ 0) :
    ((a + r) % 2 ^ padicValInt 2 r = a % 2 ^ padicValInt 2 r) ∧
    (bitOne (a + r) (padicValInt 2 r) ↔ ¬ bitOne a (padicValInt 2 r)) := by
  set k := padicValInt 2 r
  have hd : (2:ℤ) ^ k ∣ r := padicValInt_dvd r
  obtain ⟨m, hm⟩ := hd
  have hm2 : ¬ (2:ℤ) ∣ m := by
    intro h2
    obtain ⟨n, hn⟩ := h2
    have : (2:ℤ) ^ (k+1) ∣ r := ⟨n, by rw [hm, hn]; ring⟩
    have hv := (padicValInt_dvd_iff (p := 2) (k+1) r).1 this
    rcases hv with h | h
    · exact hr h
    · omega
  have hpos : (0:ℤ) < 2 ^ k := by positivity
  refine ⟨?_, ?_⟩
  · rw [hm, Int.add_mul_emod_self_left]
  · unfold bitOne
    rw [hm, Int.add_mul_ediv_left _ _ hpos.ne']
    have : m % 2 = 1 := by omega
    omega

lemma no3 (θ : ℕ → ℤ → Bool) (a r : ℤ) (hr : r ≠ 0) :
    ¬ (treeLt θ a (a + r) ∧ treeLt θ (a + r) (a + 2 * r)) := by
  rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  rw [val_add] at h1
  rw [val_add2] at h2
  obtain ⟨hres, hbit⟩ := flip a r hr
  rw [hres] at h2
  rw [hbit] at h2
  tauto

lemma no3' (θ : ℕ → ℤ → Bool) (a r : ℤ) (hr : r ≠ 0) :
    ¬ (treeLt θ (a + r) (a + 2 * r) ∧ treeLt θ (a + 2 * r) (a + 3 * r)) := by
  have := no3 θ (a + r) r hr
  have e1 : a + r + r = a + 2 * r := by ring
  have e2 : a + r + 2 * r = a + 3 * r := by ring
  rw [e1, e2] at this; exact this

/-- Structure of a violation of safety for a tree order. -/
lemma chain (θ : ℕ → ℤ → Bool) (P : List ℤ) (a r : ℤ) (hr : r ≠ 0)
    (h : compLt (treeLt θ) P a (a + r) ∧ compLt (treeLt θ) P (a + r) (a + 2 * r) ∧
      compLt (treeLt θ) P (a + 2 * r) (a + 3 * r)) :
    a ∈ P ∧ a + r ∈ P ∧ P.idxOf a < P.idxOf (a + r) ∧
      ((a + 2 * r ∈ P ∧ P.idxOf (a + r) < P.idxOf (a + 2 * r) ∧
          ((a + 3 * r ∈ P ∧ P.idxOf (a + 2 * r) < P.idxOf (a + 3 * r)) ∨ a + 3 * r ∉ P)) ∨
        (a + 2 * r ∉ P ∧ a + 3 * r ∉ P ∧ treeLt θ (a + 2 * r) (a + 3 * r))) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold compLt at h1 h2 h3
  by_cases hb : a + r ∈ P
  · have ha : a ∈ P := by tauto
    have hi : P.idxOf a < P.idxOf (a + r) := by tauto
    refine ⟨ha, hb, hi, ?_⟩
    by_cases hc : a + 2 * r ∈ P
    · left; refine ⟨hc, by tauto, ?_⟩
      by_cases hd : a + 3 * r ∈ P
      · left; exact ⟨hd, by tauto⟩
      · right; exact hd
    · right; tauto
  · exfalso
    have hc : a + 2 * r ∉ P := by tauto
    have hd : a + 3 * r ∉ P := by tauto
    exact no3' θ a r hr ⟨by tauto, by tauto⟩

/-- treeLt when the difference is odd. -/
lemma treeLt_odd (θ : ℕ → ℤ → Bool) (y z : ℤ) (h : (z - y) % 2 = 1) :
    treeLt θ y z ↔ ((y % 2 = 1) ↔ θ 0 0 = true) := by
  have hv : padicValInt 2 (z - y) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd; omega
  unfold treeLt bitOne
  rw [hv]; simp
  intro; omega

/-- treeLt with known 2-adic valuation of the difference. -/
lemma treeLt_val (θ : ℕ → ℤ → Bool) (y z : ℤ) (k : ℕ) (hk : padicValInt 2 (z - y) = k) :
    treeLt θ y z ↔ y ≠ z ∧ (bitOne y k ↔ θ k (y % 2 ^ k) = true) := by
  unfold treeLt; rw [hk]

lemma val_of (d : ℤ) (k : ℕ) (h1 : (2:ℤ) ^ k ∣ d) (h2 : ¬ (2:ℤ) ^ (k + 1) ∣ d) :
    padicValInt 2 d = k := by
  have hd : d ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have a := (padicValInt_dvd_iff (p := 2) k d).1 (by exact_mod_cast h1)
  have b := (padicValInt_dvd_iff (p := 2) (k + 1) d)
  have : ¬ (k + 1 ≤ padicValInt 2 d) := fun h => h2 (by exact_mod_cast b.2 (Or.inr h))
  omega

/-- `ν₂ d ≥ k` iff `2^k ∣ d` (for `d ≠ 0`). -/
lemma le_val_iff (d : ℤ) (hd : d ≠ 0) (k : ℕ) : k ≤ padicValInt 2 d ↔ (2:ℤ) ^ k ∣ d := by
  have := (padicValInt_dvd_iff (p := 2) k d)
  push_cast at this
  rw [this]; simp [hd]

end E94

namespace E94
open Erdos195

lemma pre_mem (x y : ℤ) : y ∈ [x, 0, 1, 6, 3] ↔ y = x ∨ y = 0 ∨ y = 1 ∨ y = 6 ∨ y = 3 := by
  simp

lemma pre_idx (x y : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6)
    (hy : y ∈ [x, 0, 1, 6, 3]) :
    ([x, 0, 1, 6, 3].idxOf y = 0 ∧ y = x) ∨ ([x, 0, 1, 6, 3].idxOf y = 1 ∧ y = 0) ∨
      ([x, 0, 1, 6, 3].idxOf y = 2 ∧ y = 1) ∨ ([x, 0, 1, 6, 3].idxOf y = 3 ∧ y = 6) ∨
      ([x, 0, 1, 6, 3].idxOf y = 4 ∧ y = 3) := by
  simp at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · simp
  · right; left; simp [h0]
  · right; right; left; simp [h1]
  · right; right; right; left; simp [h6]
  · right; right; right; right; simp [h3]

lemma unsafe_of (R : ℤ → ℤ → Prop) (P : List ℤ) (a b c d : ℤ) (hb : b - a = c - b)
    (hc : d - c = c - b) (hne : b ≠ a) (h1 : compLt R P a b) (h2 : compLt R P b c)
    (h3 : compLt R P c d) : ¬ Safe R P := by
  intro hs
  apply hs a (b - a) (by omega)
  have e1 : a + (b - a) = b := by ring
  have e2 : a + 2 * (b - a) = c := by linarith
  have e3 : a + 3 * (b - a) = d := by linarith
  rw [e1, e2, e3]
  exact ⟨h1, h2, h3⟩

/-- No violation where the third term lies in `P`. -/
lemma pre_case1 (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6)
    (hm1 : x ≠ -1) (hm4 : x ≠ -4) (hm6 : x ≠ -6) (a r : ℤ) (hr : r ≠ 0)
    (ha : a ∈ [x, 0, 1, 6, 3]) (hb : a + r ∈ [x, 0, 1, 6, 3])
    (hi : [x, 0, 1, 6, 3].idxOf a < [x, 0, 1, 6, 3].idxOf (a + r))
    (hc : a + 2 * r ∈ [x, 0, 1, 6, 3])
    (hi2 : [x, 0, 1, 6, 3].idxOf (a + r) < [x, 0, 1, 6, 3].idxOf (a + 2 * r))
    (hd : (a + 3 * r ∈ [x, 0, 1, 6, 3] ∧
        [x, 0, 1, 6, 3].idxOf (a + 2 * r) < [x, 0, 1, 6, 3].idxOf (a + 3 * r)) ∨
      a + 3 * r ∉ [x, 0, 1, 6, 3]) : False := by
  rcases pre_idx x a h0 h1 h3 h6 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
  rcases pre_idx x _ h0 h1 h3 h6 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ <;>
  rw [ia, ib] at hi <;> try omega
  all_goals
    rcases pre_idx x _ h0 h1 h3 h6 hc with ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ <;>
    rw [ib, ic] at hi2 <;> try omega
  all_goals rcases hd with ⟨hd, hi3⟩ | hd
  all_goals try (rw [pre_mem] at hd; omega)
  all_goals
    rcases pre_idx x _ h0 h1 h3 h6 hd with ⟨id, ed⟩ | ⟨id, ed⟩ | ⟨id, ed⟩ | ⟨id, ed⟩ | ⟨id, ed⟩ <;>
    rw [ic, id] at hi3 <;> omega

lemma key (θ : ℕ → ℤ → Bool) (a r : ℤ) (k : ℕ) (hk : padicValInt 2 r = k)
    (h : ¬ (bitOne (a + 2 * r) k ↔ θ k ((a + 2 * r) % 2 ^ k) = true)) :
    ¬ treeLt θ (a + 2 * r) (a + 3 * r) := by
  rw [treeLt_val θ _ _ k (by rw [val_add3]; exact hk)]; tauto

def th1 (x : ℤ) : ℕ → ℤ → Bool :=
  fun j _ => if j = 0 then false else if j = 1 then true else decide ((2 - x) / 2 ^ j % 2 ≠ 1)
def th7 : ℕ → ℤ → Bool :=
  fun j n => if j = 0 then false else if j = 1 then decide (n = 0) else false
def th16 : ℕ → ℤ → Bool :=
  fun j _ => if j = 0 then true else if j = 1 then true else false

lemma pre_safe (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6)
    (hm1 : x ≠ -1) (hm4 : x ≠ -4) (hm6 : x ≠ -6) (θ : ℕ → ℤ → Bool)
    (H : ∀ a r : ℤ, r ≠ 0 → a ∈ [x, 0, 1, 6, 3] → a + r ∈ [x, 0, 1, 6, 3] →
      [x, 0, 1, 6, 3].idxOf a < [x, 0, 1, 6, 3].idxOf (a + r) →
      a + 2 * r ∉ [x, 0, 1, 6, 3] → a + 3 * r ∉ [x, 0, 1, 6, 3] →
      ¬ treeLt θ (a + 2 * r) (a + 3 * r)) :
    Safe (treeLt θ) [x, 0, 1, 6, 3] := by
  intro a r hr h
  obtain ⟨ha, hb, hi, hrest⟩ := chain _ _ a r hr h
  rcases hrest with ⟨hc, hi2, hd⟩ | ⟨hc, hd, ht⟩
  · exact pre_case1 x h0 h1 h3 h6 hm1 hm4 hm6 a r hr ha hb hi hc hi2 hd
  · exact H a r hr ha hb hi hc hd ht

lemma f1_H (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) (hx : x % 4 = 1) (a r : ℤ) (hr : r ≠ 0)
    (ha : a ∈ [x, 0, 1, 6, 3]) (hb : a + r ∈ [x, 0, 1, 6, 3])
    (hi : [x, 0, 1, 6, 3].idxOf a < [x, 0, 1, 6, 3].idxOf (a + r))
    (hc : a + 2 * r ∉ [x, 0, 1, 6, 3]) (hd : a + 3 * r ∉ [x, 0, 1, 6, 3]) :
    ¬ treeLt (th1 x) (a + 2 * r) (a + 3 * r) := by
  rw [pre_mem] at hc hd
  rcases pre_idx x a h0 h1 h3 h6 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
  rcases pre_idx x _ h0 h1 h3 h6 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ <;>
  rw [ia, ib] at hi <;> try omega
  all_goals try (refine key _ a r 0 (val_of r 0 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th1; simp <;> omega))
  all_goals try (refine key _ a r 1 (val_of r 1 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th1; simp <;> omega))
  all_goals try (
       have hk2 : 2 ≤ padicValInt 2 r := (le_val_iff r hr 2).2 (by norm_num; omega)
       apply key _ a r _ rfl
       have e : a + 2 * r = 2 - x := by omega
       rw [e]
       unfold th1 bitOne
       simp only [show padicValInt 2 r ≠ 0 by omega, show padicValInt 2 r ≠ 1 by omega, if_false]
       generalize (2 - x) / 2 ^ padicValInt 2 r = q
       simp; omega)

lemma f7_H (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) (hx : x = 7) (a r : ℤ) (hr : r ≠ 0)
    (ha : a ∈ [x, 0, 1, 6, 3]) (hb : a + r ∈ [x, 0, 1, 6, 3])
    (hi : [x, 0, 1, 6, 3].idxOf a < [x, 0, 1, 6, 3].idxOf (a + r))
    (hc : a + 2 * r ∉ [x, 0, 1, 6, 3]) (hd : a + 3 * r ∉ [x, 0, 1, 6, 3]) :
    ¬ treeLt (th7) (a + 2 * r) (a + 3 * r) := by
  rw [pre_mem] at hc hd
  rcases pre_idx x a h0 h1 h3 h6 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
  rcases pre_idx x _ h0 h1 h3 h6 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ <;>
  rw [ia, ib] at hi <;> try omega
  all_goals try (refine key _ a r 0 (val_of r 0 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th7; simp <;> omega))
  all_goals try (refine key _ a r 1 (val_of r 1 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th7; simp <;> omega))
  all_goals try (refine key _ a r 2 (val_of r 2 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th7; simp <;> omega))

lemma f16_H (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) (hx : x = 16) (a r : ℤ) (hr : r ≠ 0)
    (ha : a ∈ [x, 0, 1, 6, 3]) (hb : a + r ∈ [x, 0, 1, 6, 3])
    (hi : [x, 0, 1, 6, 3].idxOf a < [x, 0, 1, 6, 3].idxOf (a + r))
    (hc : a + 2 * r ∉ [x, 0, 1, 6, 3]) (hd : a + 3 * r ∉ [x, 0, 1, 6, 3]) :
    ¬ treeLt (th16) (a + 2 * r) (a + 3 * r) := by
  rw [pre_mem] at hc hd
  rcases pre_idx x a h0 h1 h3 h6 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
  rcases pre_idx x _ h0 h1 h3 h6 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ <;>
  rw [ia, ib] at hi <;> try omega
  all_goals try (refine key _ a r 0 (val_of r 0 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th16; simp <;> omega))
  all_goals try (refine key _ a r 1 (val_of r 1 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th16; simp <;> omega))
  all_goals try (refine key _ a r 4 (val_of r 4 ?_ ?_) ?_ <;> first | (norm_num <;> omega) | (unfold bitOne th16; simp <;> omega))

lemma pre_unsafe (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6)
    (hx : ¬ ((x % 4 = 1 ∧ x ≠ 1) ∨ x = 7 ∨ x = 16)) (θ : ℕ → ℤ → Bool) :
    ¬ Safe (treeLt θ) [x, 0, 1, 6, 3] := by
  have ix : [x, 0, 1, 6, 3].idxOf x = 0 := by simp
  have i0 : [x, 0, 1, 6, 3].idxOf (0:ℤ) = 1 := by simp [h0]
  have i1 : [x, 0, 1, 6, 3].idxOf (1:ℤ) = 2 := by simp [h1]
  have i6 : [x, 0, 1, 6, 3].idxOf (6:ℤ) = 3 := by simp [h6]
  have i3 : [x, 0, 1, 6, 3].idxOf (3:ℤ) = 4 := by simp [h3]
  have mx : x ∈ [x, 0, 1, 6, 3] := by simp
  have m0 : (0:ℤ) ∈ [x, 0, 1, 6, 3] := by simp
  have m1 : (1:ℤ) ∈ [x, 0, 1, 6, 3] := by simp
  have m6 : (6:ℤ) ∈ [x, 0, 1, 6, 3] := by simp
  have m3 : (3:ℤ) ∈ [x, 0, 1, 6, 3] := by simp
  by_cases he : x % 2 = 0
  · by_cases h4 : x = -4
    · subst h4
      apply unsafe_of _ _ (-4) 1 6 11 (by norm_num) (by norm_num) (by norm_num) <;> unfold compLt
      · exact Or.inl ⟨mx, m1, by rw [ix, i1]; norm_num⟩
      · exact Or.inl ⟨m1, m6, by rw [i1, i6]; norm_num⟩
      · exact Or.inr (Or.inl ⟨m6, by rw [pre_mem]; norm_num⟩)
    by_cases ht : θ 0 0 = true
    · apply unsafe_of _ _ 1 6 11 16 (by norm_num) (by norm_num) (by norm_num) <;> unfold compLt
      · exact Or.inl ⟨m1, m6, by rw [i1, i6]; norm_num⟩
      · exact Or.inr (Or.inl ⟨m6, by rw [pre_mem]; omega⟩)
      · refine Or.inr (Or.inr ⟨by rw [pre_mem]; omega, by rw [pre_mem]; omega, ?_⟩)
        rw [treeLt_odd] <;> simp [ht]
    · by_cases h2 : x = 2
      · subst h2
        apply unsafe_of _ _ 2 3 4 5 (by norm_num) (by norm_num) (by norm_num) <;> unfold compLt
        · exact Or.inl ⟨mx, m3, by rw [ix, i3]; norm_num⟩
        · exact Or.inr (Or.inl ⟨m3, by rw [pre_mem]; norm_num⟩)
        · refine Or.inr (Or.inr ⟨by rw [pre_mem]; norm_num, by rw [pre_mem]; norm_num, ?_⟩)
          rw [treeLt_odd] <;> simp [ht]
      · apply unsafe_of _ _ x 1 (2 - x) (3 - 2 * x) (by ring) (by ring) (by omega) <;> unfold compLt
        · exact Or.inl ⟨mx, m1, by rw [ix, i1]; norm_num⟩
        · exact Or.inr (Or.inl ⟨m1, by rw [pre_mem]; omega⟩)
        · refine Or.inr (Or.inr ⟨by rw [pre_mem]; omega, by rw [pre_mem]; omega, ?_⟩)
          rw [treeLt_odd]
          · simp [ht]; omega
          · omega
  · have h3' : x % 4 = 3 := by omega
    by_cases hm1 : x = -1
    · subst hm1
      apply unsafe_of _ _ (-1) 0 1 2 (by norm_num) (by norm_num) (by norm_num) <;> unfold compLt
      · exact Or.inl ⟨mx, m0, by rw [ix, i0]; norm_num⟩
      · exact Or.inl ⟨m0, m1, by rw [i0, i1]; norm_num⟩
      · exact Or.inr (Or.inl ⟨m1, by rw [pre_mem]; norm_num⟩)
    by_cases ht : θ 1 1 = true
    · apply unsafe_of _ _ x 1 (2 - x) (3 - 2 * x) (by ring) (by ring) (by omega) <;> unfold compLt
      · exact Or.inl ⟨mx, m1, by rw [ix, i1]; norm_num⟩
      · exact Or.inr (Or.inl ⟨m1, by rw [pre_mem]; omega⟩)
      · refine Or.inr (Or.inr ⟨by rw [pre_mem]; omega, by rw [pre_mem]; omega, ?_⟩)
        rw [treeLt_val θ _ _ 1 (val_of _ 1 (by norm_num; omega) (by norm_num; omega))]
        have e : (2 - x) % 2 ^ 1 = 1 := by norm_num; omega
        rw [e, ht]
        unfold bitOne
        refine ⟨by omega, ?_⟩
        norm_num; omega
    · apply unsafe_of _ _ 1 3 5 7 (by norm_num) (by norm_num) (by norm_num) <;> unfold compLt
      · exact Or.inl ⟨m1, m3, by rw [i1, i3]; norm_num⟩
      · exact Or.inr (Or.inl ⟨m3, by rw [pre_mem]; omega⟩)
      · refine Or.inr (Or.inr ⟨by rw [pre_mem]; omega, by rw [pre_mem]; omega, ?_⟩)
        rw [treeLt_val θ _ _ 1 (val_of _ 1 (by norm_num) (by norm_num))]
        unfold bitOne
        norm_num
        simpa using ht

theorem prefix_ (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [x, 0, 1, 6, 3]) ↔
      (x % 4 = 1 ∧ x ≠ 1) ∨ x = 7 ∨ x = 16 := by
  constructor
  · rintro ⟨θ, hs⟩
    by_contra hx
    exact pre_unsafe x h0 h1 h3 h6 hx θ hs
  · rintro (⟨hx, -⟩ | hx | hx)
    · exact ⟨th1 x, pre_safe x h0 h1 h3 h6 (by omega) (by omega) (by omega) _
        (fun a r hr ha hb hi hc hd => f1_H x h0 h1 h3 h6 hx a r hr ha hb hi hc hd)⟩
    · exact ⟨th7, pre_safe x h0 h1 h3 h6 (by omega) (by omega) (by omega) _
        (fun a r hr ha hb hi hc hd => f7_H x h0 h1 h3 h6 hx a r hr ha hb hi hc hd)⟩
    · exact ⟨th16, pre_safe x h0 h1 h3 h6 (by omega) (by omega) (by omega) _
        (fun a r hr ha hb hi hc hd => f16_H x h0 h1 h3 h6 hx a r hr ha hb hi hc hd)⟩

end E94

open Erdos195 in
theorem solution (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [x, 0, 1, 6, 3]) ↔
      (x % 4 = 1 ∧ x ≠ 1) ∨ x = 7 ∨ x = 16 :=
  E94.prefix_ x h0 h1 h3 h6
