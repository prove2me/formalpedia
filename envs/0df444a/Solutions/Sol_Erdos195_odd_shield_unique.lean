-- Prove2me | solution 1 for Erdos195.odd_shield_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:23:47.916775+00:00
-- url     : https://prove2.me/submissions/0f5e3c9e-6aea-496c-a889-bed310122690

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

lemma idxv4 (x y : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (hy : y ∈ [0, 1, x, 3]) :
    ([0, 1, x, 3].idxOf y = 0 ∧ y = 0) ∨ ([0, 1, x, 3].idxOf y = 1 ∧ y = 1) ∨
      ([0, 1, x, 3].idxOf y = 2 ∧ y = x) ∨ ([0, 1, x, 3].idxOf y = 3 ∧ y = 3) := by
  simp at hy
  rcases hy with rfl | rfl | rfl | rfl
  · simp
  · simp
  · right; right; left; simp [Ne.symm h0, Ne.symm h1]
  · right; right; right; simp [Ne.symm h0, Ne.symm h1]; rw [List.idxOf_cons_ne _ h3]; simp

lemma not_lt_of (θ : ℕ → ℤ → Bool) (y z : ℤ) (k : ℕ) (hk : padicValInt 2 (z - y) = k)
    (h : (y / 2 ^ k % 2 = 1) ↔ ¬ θ k (y % 2 ^ k) = true) : ¬ treeLt θ y z := by
  rw [treeLt_val θ y z k hk]; unfold bitOne; tauto

theorem osu_x (x : ℤ) (hx : x % 2 = 0) (h0 : x ≠ 0) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x, 3]) ↔ x = 6 := by
  have h1 : x ≠ 1 := by omega
  have h3 : x ≠ 3 := by omega
  have mem : ∀ y : ℤ, y ∈ [0, 1, x, 3] ↔ y = 0 ∨ y = 1 ∨ y = x ∨ y = 3 := by intro y; simp
  have i0 : [0, 1, x, 3].idxOf (0:ℤ) = 0 := by simp
  have i1 : [0, 1, x, 3].idxOf (1:ℤ) = 1 := by simp
  have ix : [0, 1, x, 3].idxOf x = 2 := by simp [Ne.symm h0, Ne.symm h1]
  have i3 : [0, 1, x, 3].idxOf (3:ℤ) = 3 := by simp; rw [List.idxOf_cons_ne _ h3]; simp
  constructor
  · rintro ⟨θ, hs⟩
    by_contra h6
    by_cases h2 : x = 2
    · subst h2
      apply hs 0 1 (by norm_num)
      unfold compLt
      norm_num
    by_cases ht : θ 0 0 = true
    · apply hs 1 (x - 1) (by omega)
      have e1 : (1:ℤ) + (x - 1) = x := by ring
      rw [e1]
      unfold compLt
      refine ⟨Or.inl ⟨by simp, by simp, by rw [i1, ix]; omega⟩, Or.inr (Or.inl ⟨by simp, ?_⟩),
        Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
      · rw [mem]; omega
      · rw [mem]; omega
      · rw [mem]; omega
      · rw [treeLt_odd]
        · simp [ht]
        · omega
    · apply hs 0 3 (by norm_num)
      unfold compLt
      refine ⟨Or.inl ⟨by simp, by simp, by rw [i0]; norm_num [i3]⟩, Or.inr (Or.inl ⟨by simp, ?_⟩),
        Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
      · rw [mem]; omega
      · rw [mem]; omega
      · rw [mem]; omega
      · rw [treeLt_odd] <;> simp [ht]
  · rintro rfl
    refine ⟨fun j _ => decide (j ≠ 0), ?_⟩
    intro a r hr h
    obtain ⟨ha, hb, hi, hrest⟩ := chain _ _ a r hr h
    rcases idxv4 6 a h0 h1 h3 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
    rcases idxv4 6 (a + r) h0 h1 h3 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ <;>
    rw [ia, ib] at hi <;> try omega
    all_goals rcases hrest with ⟨hc, hi2, _⟩ | ⟨hc, hd, ht⟩
    all_goals try (rcases idxv4 6 _ h0 h1 h3 hc with ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ <;> omega)
    all_goals try (exfalso; apply hc; rw [mem]; omega)
    all_goals try (exfalso; apply hd; rw [mem]; omega)
    · -- 0,6 : 12, 18
      have e2 : a + 2 * r = 12 := by omega
      have e3 : a + 3 * r = 18 := by omega
      rw [e2, e3] at ht
      refine not_lt_of _ 12 18 1 ?_ (by decide) ht
      exact val_of _ 1 (by norm_num) (by norm_num)
    · -- 1,6 : 11, 16
      have e2 : a + 2 * r = 11 := by omega
      have e3 : a + 3 * r = 16 := by omega
      rw [e2, e3] at ht
      rw [treeLt_odd] at ht
      · simp at ht
      · norm_num
    · -- 1,3 : 5, 7
      have e2 : a + 2 * r = 5 := by omega
      have e3 : a + 3 * r = 7 := by omega
      rw [e2, e3] at ht
      refine not_lt_of _ 5 7 1 ?_ (by decide) ht
      exact val_of _ 1 (by norm_num) (by norm_num)

theorem osu (m : ℤ) (hm : m % 2 = 1) (hm0 : 1 + m ≠ 0) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 1 + m, 3]) ↔ m = 5 := by
  rw [osu_x (1 + m) (by omega) hm0]; omega

end E94

open Erdos195 in
theorem solution (m : ℤ) (hm : m % 2 = 1) (hm0 : 1 + m ≠ 0) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 1 + m, 3]) ↔ m = 5 :=
  E94.osu m hm hm0
