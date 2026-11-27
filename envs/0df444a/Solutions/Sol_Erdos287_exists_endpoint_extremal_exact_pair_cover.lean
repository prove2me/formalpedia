-- Prove2me | solution 1 for Erdos287.exists_endpoint_extremal_exact_pair_cover
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:20:30.92507+00:00
-- url     : https://prove2.me/submissions/fd31d5d6-8a52-4457-a580-279d86491bb3

import Mathlib

open Finset

set_option autoImplicit false

/-- An exact pair cover has an extremal representative. It first minimizes
the largest denominator, then maximizes the smallest denominator, and
finally minimizes the number of selected denominators. -/
theorem solution (D : Finset ℕ) (m M : ℕ) (hm : 1 < m)
    (hmD : m ∈ D) (hMD : M ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) :
    ∃ (l u : ℕ) (E : Finset ℕ), u ≤ M ∧ 1 < l ∧ l ∈ E ∧ u ∈ E ∧
      E ⊆ Finset.Icc l u ∧
      (∀ x, l ≤ x → x + 1 ≤ u → x ∈ E ∨ x + 1 ∈ E) ∧
      (∑ n ∈ E, (1 : ℚ) / n = 1) ∧
      (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
        F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
        (∑ n ∈ F, (1 : ℚ) / n = 1) →
        u ≤ b ∧ (b = u → a ≤ l) ∧ (b = u → a = l → E.card ≤ F.card)) := by
  classical
  let Good (a b : ℕ) (F : Finset ℕ) : Prop :=
    1 < a ∧ a ∈ F ∧ b ∈ F ∧ F ⊆ Icc a b ∧
      (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) ∧
      (∑ n ∈ F, (1 : ℚ) / n = 1)
  have hab {a b : ℕ} {F : Finset ℕ} (h : Good a b F) : a ≤ b :=
    (mem_Icc.mp (h.2.2.2.1 h.2.1)).2
  let Max (b : ℕ) := ∃ a F, Good a b F
  have hexMax : ∃ b, Max b := ⟨M, m, D, hm, hmD, hMD, hD, hcover, hsum⟩
  let u := Nat.find hexMax
  obtain ⟨a₀, F₀, h₀⟩ : Max u := Nat.find_spec hexMax
  let Span (d : ℕ) := ∃ a F, Good a u F ∧ u - a = d
  have hexSpan : ∃ d, Span d := ⟨u - a₀, a₀, F₀, h₀, rfl⟩
  obtain ⟨l, E₀, hl₀, hspan⟩ := Nat.find_spec hexSpan
  let Size (d : ℕ) := ∃ E, Good l u E ∧ E.card = d
  have hexSize : ∃ d, Size d := ⟨E₀.card, E₀, hl₀, rfl⟩
  obtain ⟨E, he, hsize⟩ := Nat.find_spec hexSize
  refine ⟨l, u, E, Nat.find_min' hexMax ⟨m, D, hm, hmD, hMD, hD, hcover, hsum⟩,
    he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2, ?_⟩
  intro a b F ha haF hbF hF hcov hS
  have hf : Good a b F := ⟨ha, haF, hbF, hF, hcov, hS⟩
  refine ⟨Nat.find_min' hexMax ⟨a, F, hf⟩, ?_, ?_⟩
  · intro hb
    subst b
    have hd : Nat.find hexSpan ≤ u - a := Nat.find_min' hexSpan ⟨a, F, hf, rfl⟩
    have haus := hab hf
    omega
  · intro hb ha'
    subst b
    subst a
    rw [hsize]
    exact Nat.find_min' hexSize ⟨F, hf, rfl⟩

