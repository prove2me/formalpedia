-- Prove2me | solution 1 for Erdos195.shield_mid_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:35:06.165298+00:00
-- url     : https://prove2.me/submissions/7103e644-7776-4060-82e1-a049c4aee3bf

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

lemma mid_tl (θ : ℕ → ℤ → Bool) (y z : ℤ) (k : ℕ) (h1 : (z - y) % 2 ^ k = 0)
    (h2 : (z - y) % 2 ^ (k + 1) ≠ 0) :
    treeLt θ y z ↔ y ≠ z ∧ (y / 2 ^ k % 2 = 1 ↔ θ k (y % 2 ^ k) = true) := by
  rw [treeLt_val θ y z k (val_of _ _ (Int.dvd_of_emod_eq_zero h1)
    (fun h => h2 (Int.emod_eq_zero_of_dvd h)))]; rfl


lemma safe4 : Safe (treeLt (fun j _ => decide (j ≠ 0))) [0, 1, 4, 6, 3] := by
  intro a r hr h
  obtain ⟨ha, hb, hi, hrest⟩ := chain _ _ a r hr h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  have e : r = (a + r) - a := by ring
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with hb | hb | hb | hb | hb <;> rw [hb] at e <;> subst e <;> norm_num at hi <;>
    norm_num at hrest <;> (first | (rw [mid_tl _ _ _ 0] at hrest; norm_num at hrest; all_goals decide) | (rw [mid_tl _ _ _ 1] at hrest; norm_num at hrest; all_goals decide) | (rw [mid_tl _ _ _ 2] at hrest; norm_num at hrest; all_goals decide) | (rw [mid_tl _ _ _ 3] at hrest; norm_num at hrest; all_goals decide))

lemma safe11 : Safe (treeLt (fun j _ => decide (j ≠ 3))) [0, 1, 11, 6, 3] := by
  intro a r hr h
  obtain ⟨ha, hb, hi, hrest⟩ := chain _ _ a r hr h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  have e : r = (a + r) - a := by ring
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with hb | hb | hb | hb | hb <;> rw [hb] at e <;> subst e <;> norm_num at hi <;>
    norm_num at hrest <;> (first | (rw [mid_tl _ _ _ 0] at hrest; norm_num at hrest; all_goals decide) | (rw [mid_tl _ _ _ 1] at hrest; norm_num at hrest; all_goals decide) | (rw [mid_tl _ _ _ 2] at hrest; norm_num at hrest; all_goals decide) | (rw [mid_tl _ _ _ 3] at hrest; norm_num at hrest; all_goals decide))

theorem mid (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x, 6, 3]) ↔ x = 4 ∨ x = 11 := by
  constructor
  · rintro ⟨θ, hs⟩
    by_contra hx
    have mem : ∀ y : ℤ, y ∈ [0, 1, x, 6, 3] ↔ y = 0 ∨ y = 1 ∨ y = x ∨ y = 6 ∨ y = 3 := by
      intro y; simp
    have i1 : [0, 1, x, 6, 3].idxOf (1:ℤ) = 1 := by simp
    have ix : [0, 1, x, 6, 3].idxOf x = 2 := by simp [Ne.symm h0, Ne.symm h1]
    have i6 : [0, 1, x, 6, 3].idxOf (6:ℤ) = 3 := by simp [h6]
    have i3 : [0, 1, x, 6, 3].idxOf (3:ℤ) = 4 := by simp [h3]
    rcases Int.emod_two_eq_zero_or_one x with hp | hp
    · by_cases ht : θ 0 0 = true
      · by_cases h2 : x = 2
        · subst h2
          apply hs 0 1 (by norm_num)
          unfold compLt
          simp
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
          · rw [treeLt_odd _ _ _ (by omega), ht]; simp
      · -- chain x, 3, 6-x, 9-2x
        apply hs x (3 - x) (by omega)
        have e1 : x + (3 - x) = 3 := by ring
        rw [e1]
        unfold compLt
        refine ⟨Or.inl ⟨by simp, by simp, by rw [i3, ix]; omega⟩, Or.inr (Or.inl ⟨by simp, ?_⟩),
          Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [treeLt_odd _ _ _ (by omega)]; simp [ht]; omega
    · by_cases ht : θ 0 0 = true
      · -- chain 1, 6, 11, 16
        apply hs 1 5 (by norm_num)
        unfold compLt
        refine ⟨Or.inl ⟨by simp, by simp, by norm_num [i6]⟩, Or.inr (Or.inl ⟨by simp, ?_⟩),
          Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [treeLt_odd _ _ _ (by norm_num), ht]; simp
      · -- chain 0, x, 2x, 3x
        apply hs 0 x h0
        have e1 : (0:ℤ) + x = x := by ring
        rw [e1]
        unfold compLt
        refine ⟨Or.inl ⟨by simp, by simp, by rw [ix]; simp⟩, Or.inr (Or.inl ⟨by simp, ?_⟩),
          Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [mem]; omega
        · rw [treeLt_odd _ _ _ (by omega)]; simp [ht]
  · rintro (rfl | rfl)
    · exact ⟨_, safe4⟩
    · exact ⟨_, safe11⟩

end E94

open Erdos195 in
theorem solution (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x, 6, 3]) ↔ x = 4 ∨ x = 11 :=
  E94.mid x h0 h1 h3 h6
