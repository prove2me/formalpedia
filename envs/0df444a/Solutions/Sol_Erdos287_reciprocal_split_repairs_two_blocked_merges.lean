-- Prove2me | solution 1 for Erdos287.reciprocal_split_repairs_two_blocked_merges
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:03:56.250367+00:00
-- url     : https://prove2.me/submissions/1f582f68-1ec0-42c1-870a-42ed4f3985f9

import Mathlib
import Theorems.Thm_Erdos287_cardinality_reducing_reciprocal_edit_blocked

open Finset

set_option autoImplicit false
set_option maxHeartbeats 0

/-- A reciprocal split supplies two missing neighbors that would otherwise
block two separate merges. The simultaneous replacement uses four terms
in place of five. -/
theorem solution (D : Finset ℕ) (m M k : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card) :
    let t := 24871 * k + 4282
    let v := 12540 * k + 2159
    let w := 9996 * k + 1721
    let R : Finset ℕ := {35 * t, 119 * v, 170 * v, 209 * w, 152 * w}
    let A : Finset ℕ := {60 * t, 84 * t, 70 * v, 88 * w}
    let G : Finset ℕ := {35 * t - 1, 35 * t + 1, 119 * v + 1, 209 * w + 1,
      170 * v - 1, 170 * v + 1, 152 * w - 1, 152 * w + 1}
    m < 35 * t → 170 * v ≤ M → R ⊆ D → Disjoint A D →
    ∃ n ∈ G, m ≤ n ∧ n ≤ M ∧ n ∉ D := by
  classical
  intro t v w R A G hLow hHigh hSelected hOmitted
  have hARange : A ⊆ Icc m M := by
    intro n hn
    simp only [A, mem_insert, mem_singleton] at hn
    apply mem_Icc.mpr
    dsimp only [t, v, w] at hLow hHigh hn
    omega
  have hmR : m ∉ R := by
    simp only [R, mem_insert, mem_singleton]
    dsimp only [t, v, w] at hLow ⊢
    omega
  have separated :
      35 * t ∉ ({119 * v, 170 * v, 209 * w, 152 * w} : Finset ℕ) ∧
      119 * v ∉ ({170 * v, 209 * w, 152 * w} : Finset ℕ) ∧
      170 * v ∉ ({209 * w, 152 * w} : Finset ℕ) ∧
      209 * w ∉ ({152 * w} : Finset ℕ) ∧
      60 * t ∉ ({84 * t, 70 * v, 88 * w} : Finset ℕ) ∧
      84 * t ∉ ({70 * v, 88 * w} : Finset ℕ) ∧
      70 * v ∉ ({88 * w} : Finset ℕ) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [mem_insert, mem_singleton] <;> dsimp only [t, v, w] <;> omega
  obtain ⟨hr₁, hr₂, hr₃, hr₄, ha₁, ha₂, ha₃⟩ := separated
  have hSmall : A.card < R.card := by
    simp only [A, R, card_insert_of_notMem hr₁, card_insert_of_notMem hr₂,
      card_insert_of_notMem hr₃, card_insert_of_notMem hr₄, card_insert_of_notMem ha₁,
      card_insert_of_notMem ha₂, card_insert_of_notMem ha₃, card_singleton]
    decide
  have scale {a b c s : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
      (h : (1 : ℚ) / a + 1 / b = 1 / c) :
      (1 : ℚ) / ((a * s : ℕ) : ℚ) + 1 / ((b * s : ℕ) : ℚ) =
        1 / ((c * s : ℕ) : ℚ) := by
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha
    have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
    have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
    have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
    push_cast
    convert congrArg (fun q : ℚ => q / (s : ℚ)) h using 1 <;> field_simp
  have hSplit := scale (a := 60) (b := 84) (c := 35) (s := t)
    (by decide) (by decide) (by decide) (by dsimp [t]; omega) (by norm_num)
  have hFirst := scale (a := 119) (b := 170) (c := 70) (s := v)
    (by decide) (by decide) (by decide) (by dsimp [v]; omega) (by norm_num)
  have hSecond := scale (a := 209) (b := 152) (c := 88) (s := w)
    (by decide) (by decide) (by decide) (by dsimp [w]; omega) (by norm_num)
  have hMass : ∑ n ∈ A, (1 : ℚ) / n = ∑ n ∈ R, (1 : ℚ) / n := by
    simp only [A, R, sum_insert hr₁, sum_insert hr₂, sum_insert hr₃, sum_insert hr₄,
      sum_insert ha₁, sum_insert ha₂, sum_insert ha₃, sum_singleton]
    linarith only [hSplit, hFirst, hSecond]
  have hSeparated (x : ℕ) (hx : x ∈ R) : x + 1 ∉ R := by
    simp only [R, mem_insert, mem_singleton] at hx ⊢
    dsimp only [t, v, w] at hx ⊢
    omega
  have hNeighbors (x y : ℕ) (hx : x ∈ R) (hy : x + 1 = y ∨ y + 1 = x) :
      y ∈ A ∨ y ∈ G := by
    simp only [R, A, G, mem_insert, mem_singleton] at hx ⊢
    dsimp only [t, v, w] at hx ⊢
    omega
  obtain ⟨x, hx, hxx, h | h | h⟩ := Erdos287.cardinality_reducing_reciprocal_edit_blocked
    D R A m M hm hD hcover hsum hmin hSelected hmR hARange hOmitted hMass hSmall
  · exact (hSeparated x h.1 h.2).elim
  · obtain ⟨hr, hd, ha⟩ := h
    exact ⟨x + 1, (hNeighbors x (x + 1) hr (Or.inl rfl)).resolve_left ha,
      by omega, hxx, hd⟩
  · obtain ⟨hr, hd, ha⟩ := h
    exact ⟨x, (hNeighbors (x + 1) x hr (Or.inr rfl)).resolve_left ha,
      hx, by omega, hd⟩

