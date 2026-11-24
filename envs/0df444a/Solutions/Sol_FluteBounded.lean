-- Prove2me | solution 1 for FluteBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:11:39.048912+00:00
-- url     : https://prove2.me/submissions/bd0e9972-4f5b-46cb-94cc-cfd89b90031f

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Theorems.Thm_FluteReduction

set_option autoImplicit true

theorem _root_.solution (n : ℕ) (hn: n>0) (f : flute n) : ∀ i ≤ n-1, f.a i ≤ Nat.fib n := by
  -- note the statement is false without hn
  suffices : ∃ l, ∀ i ≤ n-1, ((i ≠ l → f.a i ≤ Nat.fib (n-2+1)) ∧ (i=l → f.a i ≤ Nat.fib n)) -- we strengthen the inductive hypothesis to avoid having to do everything twice
  · rcases this with ⟨l, hl⟩
    intro i hi
    match n with
    | 0 => linarith
    | 1 =>
      simp at *
      simp [hi, f.hd]
    | n+2 =>
      simp at hl
      specialize hl i (by omega)
      by_cases hil : i=l
      exact hl.2 hil
      have := hl.1 hil
      have : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
      omega
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => linarith
  | 1 =>
    use 0
    intro i hi
    simp at *
    exact ⟨(by omega), (by simp [hi, f.hd])⟩
  | 2 =>
    use 2
    intro i hi
    simp at *
    apply And.intro _ (by omega)
    have h₀ := f.hd
    have h₁ : f.a 1 = 1 := by
      have := f.period 0
      simp [f.hd] at this
      rw [←this]
    match i with
    | 0 => simp [h₀]
    | 1 => simp [h₁]
    | i+2 => linarith
  | n+3 =>
    have h₁ := ih (n+2) (by linarith) (by linarith)
    simp at *
    have hh : 0 < Nat.fib (n+2) := Nat.fib_pos.mpr (by omega)
    have hh₂ : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
    have hh₃ : Nat.fib (n+3) = Nat.fib (n+1) + Nat.fib (n+2) := Nat.fib_add_two
    rcases FluteReduction _ f with (h₂ | h₂) | h₂
    let g := aux_1 n f h₂ -- case 1: f.a 1 = 1
    use n+3 ; intros i hi
    apply And.intro _ (by omega)
    intro
    match i with
    | 0 =>
      simp [f.hd, hh, add_assoc]
      omega
    | 1 =>
      simp [h₂, add_assoc]
      omega
    | i+2 =>
      specialize h₁ g
      rcases h₁ with ⟨l, h₁⟩
      specialize h₁ (i+1) (by omega)
      have hg : g.a = a_1 n f h₂ := rfl ; rw [hg] at h₁ ; unfold a_1 at h₁ ; simp at h₁
      simp [add_assoc]
      by_cases hi₂ : n ≤ i
      have : i = n := by omega
      rw [this]
      have : f.a (n+2) = 1 := by
        have := f.period 0
        simp [f.hd] at this
        rw [←this]
      simp [this, hh]
      omega
      simp [hi₂, add_assoc] at h₁
      by_cases hil : i+1 = l
      exact h₁.2 hil
      have := h₁.1 hil
      omega
    let g := aux_2 n f h₂ -- case 2 : f.a (n+1) = 1
    simp [add_assoc] at h₂
    use n+3 ; intros i hi ; apply And.intro _ (by omega)
    intro
    by_cases hi₂ : i = n+1
    simp [hi₂, h₂, hh, add_assoc] ; omega
    by_cases hi₃ : i = n+2
    have := f.period 0
    simp at this ; simp [add_assoc, hi₃, ←this, f.hd, hh] ; omega
    rcases h₁ g with ⟨l, h₁⟩
    specialize h₁ i (by omega)
    have hi₄ : ¬ n+1 ≤ i := by omega
    have hg : g.a = a_2 n f h₂ := rfl ; rw [hg] at h₁ ; unfold a_2 at h₁ ; simp [hi₄] at h₁
    by_cases hil : i = l
    exact h₁.2 hil
    have := h₁.1 hil
    simp [add_assoc] ; omega
    rcases h₂ with ⟨j, hj⟩
    simp at hj ; simp [add_assoc]
    let g := aux_3 n f j hj -- case 3 : ∃ i ≤ n, f.a (i+1) = f.a i + f.a (i+2)
    have key₁ : ∀ i ≤ n+2, i ≠ j+1 → f.a i ≤ Nat.fib (n+2) := by
      intro i hi hij
      by_cases hij : i≤j
      rcases h₁ g with ⟨l, h₁⟩
      specialize h₁ i (by omega)
      have hi₂ : ¬ n+1 ≤ i := by omega
      have hg : g.a = a_3 n f j hj := rfl ; rw [hg] at h₁ ; unfold a_3 at h₁ ; simp [hij, hi₂] at h₁
      omega
      have hij : ¬ i≤j+1 := by omega
      rcases h₁ g with ⟨l, h₁⟩
      specialize h₁ (i-1) (by omega)
      have hg : g.a = a_3 n f j hj := rfl ; rw [hg] at h₁ ; unfold a_3 at h₁ ; simp [hij] at h₁
      by_cases hi₃ : n+1 ≤ i-1
      have hi₄ : i = n+2 := by omega
      rw [hi₄]
      have := f.period 0
      simp [f.hd] at this
      have : Nat.fib (n+2) > 0 := Nat.fib_pos.mpr (by omega)
      omega
      have hi₄ : ¬ i - 1 ≤ j := by omega
      simp [hi₃, hi₄, @Nat.sub_add_cancel i 1 (by omega)] at h₁
      split_ifs at h₁ <;> omega
    use j+1 ; intro i hi
    by_cases hij : i = j+1
    · rw [hij, hj.2]
      specialize ih (n+1) (by omega) (by omega)
      apply And.intro (by omega)
      intro
      rcases h₁ g with ⟨l, h₁⟩
      by_cases hjl : l = j+1
      have hf₁ := (h₁ j (by omega)).1 (by omega)
      have hg1 : g.a = a_3 n f j hj := rfl ; rw [hg1] at hf₁ ; unfold a_3 at hf₁ ; simp [hjl] at hf₁
      split_ifs at hf₁ <;> try omega
      have hf₂ := (h₁ (j+1) (by omega)).2 (by omega)
      have hg2 : g.a = a_3 n f j hj := rfl ; rw [hg2] at hf₂ ; unfold a_3 at hf₂ ; simp [hjl] at hf₂
      by_cases hj : n ≤ j
      simp [hj] at hf₂
      have hj : j = n := by omega
      rw [hj] ; rw [hj] at hf₁
      have := f.period 0
      simp [f.hd] at this ; omega
      simp [hj, add_assoc] at hf₂ ; omega
      have hf₁ := (h₁ (j+1) (by omega)).1 (by omega)
      have hf₂ := key₁ j (by omega) (by omega)
      have hg3 : g.a = a_3 n f j hj := rfl ; rw [hg3] at hf₁ ; unfold a_3 at hf₁ ; simp [hj] at hf₁
      by_cases hj : n ≤ j
      have hj : j = n := by omega
      rw [hj] ; rw [hj] at hf₂
      have := f.period 0
      simp [f.hd] at this
      have : Nat.fib (n+1) > 0 := Nat.fib_pos.mpr (by omega)
      omega
      simp [hj, add_assoc] at hf₁ ; omega
    · have := key₁ i hi hij
      exact ⟨(by omega), (by omega)⟩
