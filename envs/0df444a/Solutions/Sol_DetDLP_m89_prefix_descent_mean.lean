-- Prove2me | solution 1 for DetDLP.m89_prefix_descent_mean
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:52:57.433249+00:00
-- url     : https://prove2.me/submissions/1f065961-6d2a-436e-8f35-c07665f29704

import Definitions.Def_DetDLP_M89_SeedSelection
set_option autoImplicit false
open DetDLP.M89SeedSelection

namespace DetDLP.M89SeedSelection
private theorem pick {α : Type*} (count : α → ℕ) (cost : α → ℝ) (parent l r : α)
    (hne : 0 < count parent) (hc : count parent = count l + count r)
    (hs : cost parent = cost l + cost r) (hz : ∀ a, count a = 0 → cost a = 0) :
    let a := if goRight count cost l r then r else l
    0 < count a ∧ cost a / count a ≤ cost parent / count parent := by
  have hp : (0 : ℝ) < count parent := by exact_mod_cast hne
  have hc' : (count parent : ℝ) = count l + count r := by exact_mod_cast hc
  by_cases hl : count l = 0
  · have hr : 0 < count r := by omega
    simp only [goRight, hl, true_or, decide_true, if_true]
    refine ⟨hr, ?_⟩
    rw [hs, hz l hl, zero_add, hc, hl, zero_add]
  by_cases hr : count r = 0
  · simp [goRight, hl, hr, hs, hc, hz r hr, Nat.pos_of_ne_zero hl]
  have hL : (0 : ℝ) < count l := by exact_mod_cast Nat.pos_of_ne_zero hl
  have hR : (0 : ℝ) < count r := by exact_mod_cast Nat.pos_of_ne_zero hr
  by_cases ht : cost r * count l < cost l * count r
  · have hb : goRight count cost l r = true := by simp [goRight, hl, hr, ht]
    simp only [hb, if_true]
    refine ⟨Nat.pos_of_ne_zero hr, (div_le_div_iff₀ hR hp).2 ?_⟩
    rw [hc', hs]
    linarith
  · simp [goRight, hl, hr, ht]
    constructor
    · omega
    · apply (div_le_div_iff₀ hL hp).2
      rw [hc', hs]
      linarith
end DetDLP.M89SeedSelection

theorem solution {α : Type*} (count : α → ℕ) (cost : α → ℝ) (children : α → Bool → α)
    (hz : ∀ a, count a = 0 → cost a = 0) (good : ℕ → α → Prop)
    (split : ∀ k a, good (k+1) a → count a = count (children a false) + count (children a true) ∧
      cost a = cost (children a false) + cost (children a true) ∧ ∀ b, good k (children a b))
    (k : ℕ) (a : α) (hg : good k a) (hne : 0 < count a) :
    let z := descend count cost children k a
    good 0 z ∧ 0 < count z ∧ cost z / count z ≤ cost a / count a := by
  induction k generalizing a with
  | zero => exact ⟨hg, hne, le_rfl⟩
  | succ k ih =>
    obtain ⟨hc, hs, hbelow⟩ := split k a hg
    let b := goRight count cost (children a false) (children a true)
    have h := pick count cost a (children a false) (children a true) hne hc hs hz
    have hchild : 0 < count (children a b) ∧ cost (children a b) / count (children a b) ≤ cost a / count a := by
      change let x := if b then children a true else children a false; 0 < count x ∧ cost x / count x ≤ cost a / count a at h
      cases hb : b <;> simp [hb] at h ⊢ <;> exact h
    obtain ⟨hg0, hp, hle⟩ := ih (children a b) (hbelow b) hchild.1
    exact ⟨hg0, hp, hle.trans hchild.2⟩


#print axioms solution
