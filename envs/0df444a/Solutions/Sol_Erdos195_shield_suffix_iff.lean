-- Prove2me | solution 1 for Erdos195.shield_suffix_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:31:02.123318+00:00
-- url     : https://prove2.me/submissions/a0af5c45-b2fa-4d7b-af56-a84518d1053c

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

lemma suf_idx (x y : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6)
    (hy : y ∈ [0, 1, 6, 3, x]) :
    ([0, 1, 6, 3, x].idxOf y = 0 ∧ y = 0) ∨ ([0, 1, 6, 3, x].idxOf y = 1 ∧ y = 1) ∨
      ([0, 1, 6, 3, x].idxOf y = 2 ∧ y = 6) ∨ ([0, 1, 6, 3, x].idxOf y = 3 ∧ y = 3) ∨
      ([0, 1, 6, 3, x].idxOf y = 4 ∧ y = x) := by
  simp at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · right; right; right; right; simp [Ne.symm h0, Ne.symm h1, Ne.symm h3, Ne.symm h6]

lemma suf_notSafe (θ : ℕ → ℤ → Bool) (P : List ℤ) (a b c d : ℤ) (h1 : b - a ≠ 0)
    (h2 : c = 2 * b - a) (h3 : d = 3 * b - 2 * a)
    (hab : compLt (treeLt θ) P a b) (hbc : compLt (treeLt θ) P b c)
    (hcd : compLt (treeLt θ) P c d) : ¬ Safe (treeLt θ) P := by
  intro hs
  apply hs a (b - a) h1
  have e1 : a + (b - a) = b := by ring
  have e2 : a + 2 * (b - a) = c := by rw [h2]; ring
  have e3 : a + 3 * (b - a) = d := by rw [h3]; ring
  rw [e1, e2, e3]
  exact ⟨hab, hbc, hcd⟩

/-- The witness used for the `←` direction. -/
def sufTh (j : ℕ) (r : ℤ) : Bool := if j = 0 then false else if j = 1 then true else decide (r ≠ 2)

lemma suf_odd (y z : ℤ) (h : (z - y) % 2 = 1) (hy : y % 2 = 1) : ¬ treeLt sufTh y z := by
  rw [treeLt_odd _ _ _ h]; simp [sufTh, hy]

lemma suf_v1 (y z : ℤ) (h : (z - y) % 4 = 2) (hy : y / 2 % 2 = 0) : ¬ treeLt sufTh y z := by
  have hv : padicValInt 2 (z - y) = 1 :=
    val_of _ 1 (by rw [Int.dvd_iff_emod_eq_zero]; omega) (by rw [Int.dvd_iff_emod_eq_zero]; omega)
  rw [treeLt_val _ _ _ 1 hv]
  unfold bitOne
  simp [sufTh, hy]

lemma suf_4 : ¬ treeLt sufTh 8 12 := by
  have hv : padicValInt 2 (12 - 8) = 2 := val_of _ 2 (by norm_num) (by norm_num)
  rw [treeLt_val _ _ _ 2 hv]
  unfold bitOne
  simp [sufTh]

lemma suf_6x (x : ℤ) (hx : x % 4 = 2) (h6 : x ≠ 6) :
    ¬ treeLt sufTh (2 * x - 6) (3 * x - 12) := by
  have hne : x - 6 ≠ 0 := by omega
  set m := padicValInt 2 (3 * x - 12 - (2 * x - 6)) with hm
  have e : 3 * x - 12 - (2 * x - 6) = x - 6 := by ring
  rw [e] at hm
  have hm2 : 2 ≤ m := by
    rw [hm, le_val_iff _ hne]; rw [Int.dvd_iff_emod_eq_zero]; norm_num <;> omega
  have hdvd : (2:ℤ) ^ m ∣ x - 6 := by rw [hm]; exact padicValInt_dvd _
  obtain ⟨q, hq⟩ := hdvd
  have hM : (0:ℤ) < 2 ^ m := by positivity
  have ey : 2 * x - 6 = 6 + 2 ^ m * (2 * q) := by linear_combination 2 * hq
  unfold treeLt
  rw [e, ← hm, ey]
  intro ⟨_, h⟩
  unfold bitOne at h
  rw [Int.add_mul_ediv_left _ _ hM.ne', Int.add_mul_emod_self_left 6 (2 ^ m) (2 * q)] at h
  rcases Nat.eq_or_lt_of_le hm2 with h2 | h3
  · rw [← h2] at h; simp [sufTh] at h
  · have h8 : (8:ℤ) ≤ 2 ^ m := by
      calc (8:ℤ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) h3
    have q1 : (6:ℤ) / 2 ^ m = 0 := Int.ediv_eq_zero_of_lt (by norm_num) (by omega)
    have q2 : (6:ℤ) % 2 ^ m = 6 := Int.emod_eq_of_lt (by norm_num) (by omega)
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    rw [q1, q2] at h
    simp [sufTh, hm0, hm1] at h

theorem suffix (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 6, 3, x]) ↔ x % 4 = 2 ∨ x = 4 := by
  have mem : ∀ y : ℤ, y ∈ [0, 1, 6, 3, x] ↔ y = 0 ∨ y = 1 ∨ y = 6 ∨ y = 3 ∨ y = x := by
    intro y; simp
  have ix : [0, 1, 6, 3, x].idxOf x = 4 := by
    simp [Ne.symm h0, Ne.symm h1, Ne.symm h3, Ne.symm h6]
  constructor
  · rintro ⟨θ, hs⟩
    by_contra hx
    revert hs
    by_cases hodd : x % 2 = 1
    · by_cases ht : θ 0 0 = true
      · by_cases h11 : x = 11
        · subst h11
          apply suf_notSafe θ _ 1 6 11 16 (by norm_num) (by norm_num) (by norm_num)
          · exact Or.inl ⟨by simp, by simp, by simp⟩
          · exact Or.inl ⟨by simp, by simp, by simp⟩
          · exact Or.inr (Or.inl ⟨by simp, by simp⟩)
        · apply suf_notSafe θ _ 1 6 11 16 (by norm_num) (by norm_num) (by norm_num)
          · exact Or.inl ⟨by simp, by simp, by simp⟩
          · exact Or.inr (Or.inl ⟨by simp, by rw [mem]; omega⟩)
          · refine Or.inr (Or.inr ⟨by rw [mem]; omega, by rw [mem]; omega, ?_⟩)
            rw [treeLt_odd _ _ _ (by norm_num)]; simp [ht]
      · apply suf_notSafe θ _ 0 x (2 * x) (3 * x) (by omega) (by ring) (by ring)
        · exact Or.inl ⟨by simp, by simp, by rw [ix]; simp⟩
        · exact Or.inr (Or.inl ⟨by simp, by rw [mem]; omega⟩)
        · refine Or.inr (Or.inr ⟨by rw [mem]; omega, by rw [mem]; omega, ?_⟩)
          rw [treeLt_odd _ _ _ (by omega)]; simp [ht]
    · have h4 : x % 4 = 0 := by omega
      by_cases h12 : x = 12
      · subst h12
        apply suf_notSafe θ _ 0 6 12 18 (by norm_num) (by norm_num) (by norm_num)
        · exact Or.inl ⟨by simp, by simp, by simp⟩
        · exact Or.inl ⟨by simp, by simp, by simp⟩
        · exact Or.inr (Or.inl ⟨by simp, by simp⟩)
      by_cases ht : θ 1 0 = true
      · apply suf_notSafe θ _ 6 x (2 * x - 6) (3 * x - 12) (by omega) (by ring) (by ring)
        · exact Or.inl ⟨by simp, by simp, by rw [ix]; simp⟩
        · exact Or.inr (Or.inl ⟨by simp, by rw [mem]; omega⟩)
        · refine Or.inr (Or.inr ⟨by rw [mem]; omega, by rw [mem]; omega, ?_⟩)
          have hv : padicValInt 2 (3 * x - 12 - (2 * x - 6)) = 1 :=
            val_of _ 1 (by rw [Int.dvd_iff_emod_eq_zero]; omega)
              (by rw [Int.dvd_iff_emod_eq_zero]; omega)
          rw [treeLt_val _ _ _ 1 hv]
          unfold bitOne
          have r0 : (2 * x - 6) % 2 ^ 1 = 0 := by omega
          rw [r0]
          refine ⟨by omega, ?_⟩
          simp [ht] <;> omega
      · apply suf_notSafe θ _ 0 6 12 18 (by norm_num) (by norm_num) (by norm_num)
        · exact Or.inl ⟨by simp, by simp, by simp⟩
        · exact Or.inr (Or.inl ⟨by simp, by rw [mem]; omega⟩)
        · refine Or.inr (Or.inr ⟨by rw [mem]; omega, by rw [mem]; omega, ?_⟩)
          have hv : padicValInt 2 (18 - 12) = 1 := val_of _ 1 (by norm_num) (by norm_num)
          rw [treeLt_val _ _ _ 1 hv]
          unfold bitOne
          simp [ht]
  · intro hx
    refine ⟨sufTh, ?_⟩
    intro a r hr h
    obtain ⟨ha, hb, hi, hrest⟩ := chain _ _ a r hr h
    rcases suf_idx x a h0 h1 h3 h6 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
    rcases suf_idx x (a + r) h0 h1 h3 h6 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ |
      ⟨ib, eb⟩ <;>
    rw [ia, ib] at hi <;> try omega
    all_goals rcases hrest with ⟨hc, hi2, ⟨hd, hi3⟩ | hd⟩ | ⟨hc, hd, ht⟩
    all_goals try (rcases suf_idx x _ h0 h1 h3 h6 hc with ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ |
      ⟨ic, ec⟩ | ⟨ic, ec⟩ <;>
      rcases suf_idx x _ h0 h1 h3 h6 hd with ⟨id, ed⟩ | ⟨id, ed⟩ | ⟨id, ed⟩ | ⟨id, ed⟩ |
      ⟨id, ed⟩ <;> omega)
    all_goals try (rcases suf_idx x _ h0 h1 h3 h6 hc with ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ |
      ⟨ic, ec⟩ | ⟨ic, ec⟩ <;> rw [mem] at hd <;> omega)
    all_goals rw [mem] at hc hd
    all_goals try omega
    all_goals rcases hx with hx | hx <;> first
      | exact suf_odd _ _ (by omega) (by omega) ht
      | exact suf_v1 _ _ (by omega) (by omega) ht
      | (have e2 : a + 2 * r = 8 := by omega
         have e3 : a + 3 * r = 12 := by omega
         rw [e2, e3] at ht; exact suf_4 ht)
      | (have e2 : a + 2 * r = 2 * x - 6 := by omega
         have e3 : a + 3 * r = 3 * x - 12 := by omega
         rw [e2, e3] at ht; exact suf_6x x (by omega) h6 ht)

end E94

open Erdos195 in
theorem solution (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 6, 3, x]) ↔ x % 4 = 2 ∨ x = 4 :=
  E94.suffix x h0 h1 h3 h6
