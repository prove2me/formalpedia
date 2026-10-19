-- Prove2me | solution 1 for DiazModulus.five_point_sumset_rigid
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:04:51.803211+00:00
-- url     : https://prove2.me/submissions/354766a1-477f-465a-ae13-944c5f9cedfc

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A two-by-three sumset inside `{−k, −1, 0, 1, m}` is rigid

Let `4 ≤ k`, `2 ≤ m` and `S = {−k, −1, 0, 1, m}`, and let `A`, `B` be finite sets of integers with
two and three elements and `A + B ⊆ S`. Write `A = {a, a + d}` with `d ≥ 1`. For each of the three
`b ∈ B` both `s = a + b` and `s + d` lie in `S`, so the difference `d` is taken at three distinct
lower ends `s`. The ten positive differences of `S` (`pair`, listed by their lower end) are
`1, 1, 2, m − 1, m, m + 1, k − 1, k, k + 1, k + m`, and since `k − 1 ≥ 3` the only value taken at
three lower ends is `d = 1` with `m = 2`, at `s = −1, 0, 1`. Hence `a + B = {−1, 0, 1}`, `m = 2`
and `A + B = {−1, 0, 1} ∪ {0, 1, 2} = {−1, 0, 1, 2}` (`main`). The hypothesis `m ≤ k` is not
needed.
-/

namespace R16_fivePoint

open Pointwise

theorem mem_five {k m s : ℤ} :
    s ∈ ({-k, -1, 0, 1, m} : Finset ℤ) ↔ s = -k ∨ s = -1 ∨ s = 0 ∨ s = 1 ∨ s = m := by
  simp

/-- The pairs `s < t` of elements of `{−k, −1, 0, 1, m}`, listed by their lower end `s`. -/
theorem pair {k m s t : ℤ} (hk : 4 ≤ k) (hm : 2 ≤ m)
    (hs : s ∈ ({-k, -1, 0, 1, m} : Finset ℤ)) (ht : t ∈ ({-k, -1, 0, 1, m} : Finset ℤ))
    (hst : s < t) :
    (s = -k ∧ (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = m)) ∨ (s = -1 ∧ (t = 0 ∨ t = 1 ∨ t = m)) ∨
      (s = 0 ∧ (t = 1 ∨ t = m)) ∨ (s = 1 ∧ t = m) := by
  rw [mem_five] at hs ht
  rcases hs with h | h | h | h | h <;> rcases ht with h' | h' | h' | h' | h' <;> omega

/-- The statement for `A = {x, y}` with `x < y` and `B = {b₁, b₂, b₃}`. -/
theorem main {k m x y b₁ b₂ b₃ : ℤ} (hk : 4 ≤ k) (hm : 2 ≤ m) (hxy : x < y)
    (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃)
    (hAB : ({x, y} : Finset ℤ) + {b₁, b₂, b₃} ⊆ ({-k, -1, 0, 1, m} : Finset ℤ)) :
    m = 2 ∧ ({x, y} : Finset ℤ) + {b₁, b₂, b₃} = ({-1, 0, 1, 2} : Finset ℤ) := by
  have mem : ∀ a ∈ ({x, y} : Finset ℤ), ∀ b ∈ ({b₁, b₂, b₃} : Finset ℤ),
      a + b ∈ ({-k, -1, 0, 1, m} : Finset ℤ) := fun a ha b hb => hAB (Finset.add_mem_add ha hb)
  have r₁ := pair hk hm (mem x (by simp) b₁ (by simp)) (mem y (by simp) b₁ (by simp))
    (by omega)
  have r₂ := pair hk hm (mem x (by simp) b₂ (by simp)) (mem y (by simp) b₂ (by simp))
    (by omega)
  have r₃ := pair hk hm (mem x (by simp) b₃ (by simp)) (mem y (by simp) b₃ (by simp))
    (by omega)
  -- the common difference `y − x` is taken at the three distinct lower ends `x + bᵢ`
  have key : m = 2 ∧ y = x + 1 ∧ (x + b₁ = -1 ∨ x + b₁ = 0 ∨ x + b₁ = 1) ∧
      (x + b₂ = -1 ∨ x + b₂ = 0 ∨ x + b₂ = 1) ∧ (x + b₃ = -1 ∨ x + b₃ = 0 ∨ x + b₃ = 1) := by
    omega
  refine ⟨key.1, ?_⟩
  ext z
  simp only [Finset.mem_add, Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or,
    exists_eq_left]
  constructor <;> intro h <;> omega

end R16_fivePoint

-- The statement's `hmk : m ≤ k` is not needed.
set_option linter.unusedVariables false in
open DiazModulus Pointwise R16_fivePoint in
theorem solution (k m : ℤ) (hk : 4 ≤ k) (hm : 2 ≤ m) (hmk : m ≤ k)
    (A B : Finset ℤ) (hA : A.card = 2) (hB : B.card = 3)
    (hAB : A + B ⊆ ({-k, -1, 0, 1, m} : Finset ℤ)) :
    m = 2 ∧ A + B = ({-1, 0, 1, 2} : Finset ℤ) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hA
  obtain ⟨b₁, b₂, b₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hB
  rcases hxy.lt_or_gt with h | h
  · exact main hk hm h h12 h13 h23 hAB
  · rw [Finset.pair_comm] at hAB ⊢
    exact main hk hm h h12 h13 h23 hAB
