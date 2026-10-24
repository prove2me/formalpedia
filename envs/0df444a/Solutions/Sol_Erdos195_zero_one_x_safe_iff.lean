-- Prove2me | solution 1 for Erdos195.zero_one_x_safe_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:20:10.351352+00:00
-- url     : https://prove2.me/submissions/c89c5875-74bb-48dd-ac49-9070db5ec489

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

end E94

namespace E94
open Erdos195

lemma idxv3 (x y : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (hy : y ∈ [0, 1, x]) :
    ([0, 1, x].idxOf y = 0 ∧ y = 0) ∨ ([0, 1, x].idxOf y = 1 ∧ y = 1) ∨
      ([0, 1, x].idxOf y = 2 ∧ y = x) := by
  simp at hy
  rcases hy with rfl | rfl | rfl
  · simp
  · simp
  · right; right; simp [Ne.symm h0, Ne.symm h1]

/-- `ν₂ d ≠ 0` for even nonzero `d`. -/
lemma val_ne_zero (d : ℤ) (hd : d ≠ 0) (he : d % 2 = 0) : padicValInt 2 d ≠ 0 := by
  have h2 := (padicValInt_dvd_iff (p := 2) 1 d).1 (by norm_num; omega)
  omega

theorem zox (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x]) ↔ x % 2 = 1 := by
  have mem : ∀ y : ℤ, y ∈ [0, 1, x] ↔ y = 0 ∨ y = 1 ∨ y = x := by intro y; simp
  have i1 : [0, 1, x].idxOf (1:ℤ) = 1 := by simp
  have ix : [0, 1, x].idxOf x = 2 := by simp [Ne.symm h0, Ne.symm h1]
  constructor
  · rintro ⟨θ, hs⟩
    by_contra hx
    by_cases ht : θ 0 0 = true
    · -- chain 1, x, 2x-1, 3x-2
      apply hs 1 (x - 1) (by omega)
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
    · -- chain 0,1,2,3
      apply hs 0 1 (by norm_num)
      unfold compLt
      by_cases h2 : x = 2
      · subst h2; simp
      · refine ⟨Or.inl ⟨by simp, by simp, by simp⟩, Or.inr (Or.inl ⟨by simp, ?_⟩),
          Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [treeLt_odd] <;> simp [ht]
  · intro hx
    refine ⟨fun j _ => if j = 0 then true else decide ((2 * x - 1) / 2 ^ j % 2 ≠ 1), ?_⟩
    intro a r hr h
    obtain ⟨ha, hb, hi, hrest⟩ := chain _ _ a r hr h
    rcases idxv3 x a h0 h1 ha with ⟨ia, ea⟩ | ⟨ia, ea⟩ | ⟨ia, ea⟩ <;>
    rcases idxv3 x (a + r) h0 h1 hb with ⟨ib, eb⟩ | ⟨ib, eb⟩ | ⟨ib, eb⟩ <;>
    rw [ia, ib] at hi <;> try omega
    all_goals rcases hrest with ⟨hc, hi2, _⟩ | ⟨hc, hd, ht⟩
    all_goals try (rcases idxv3 x _ h0 h1 hc with ⟨ic, ec⟩ | ⟨ic, ec⟩ | ⟨ic, ec⟩ <;> omega)
    · -- 0,1
      rw [treeLt_odd] at ht
      · simp at ht; omega
      · omega
    · -- 0,x
      rw [treeLt_odd] at ht
      · simp at ht; omega
      · omega
    · -- 1,x : r = x - 1
      have hr1 : r = x - 1 := by omega
      have hk := val_ne_zero (x - 1) (by omega) (by omega)
      obtain ⟨_, ht⟩ := ht
      have e : a + 3 * r - (a + 2 * r) = x - 1 := by rw [hr1]; ring
      have e2 : a + 2 * r = 2 * x - 1 := by rw [hr1, ea]; ring
      rw [e, e2] at ht
      unfold bitOne at ht
      simp [hk] at ht
      generalize (2 * x - 1) / 2 ^ padicValInt 2 (x - 1) = q at ht
      omega

end E94

open Erdos195 in
theorem solution (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x]) ↔ x % 2 = 1 :=
  E94.zox x h0 h1
