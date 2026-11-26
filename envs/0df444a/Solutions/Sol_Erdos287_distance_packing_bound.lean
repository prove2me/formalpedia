-- Prove2me | solution 1 for Erdos287.distance_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:19:09.02381+00:00
-- url     : https://prove2.me/submissions/1574ebd0-6c8f-4bcf-aa81-a8e660197b63

import Mathlib

open Finset

set_option autoImplicit false

/-- An interval of forbidden differences enforces a density bound on occupied locations. -/
theorem solution (N u v : ℕ) (S : Finset ℕ) (hu : 0 < u) (hv : 2 * u ≤ v + 2)
    (hN : ∀ s ∈ S, s < N)
    (havoid : ∀ x ∈ S, ∀ y ∈ S, u ≤ y - x → v < y - x) :
    (u + v) * S.card ≤ u * (N + v) := by
  classical
  induction N using Nat.strong_induction_on generalizing S with
  | h N ih =>
    rcases eq_empty_or_nonempty S with rfl | hS
    · simp
    let a := S.min' hS
    let B := S.filter (fun s => s < a + u)
    have ha : a ∈ S := S.min'_mem hS
    have hB : B.Nonempty := ⟨a, mem_filter.mpr ⟨ha, by omega⟩⟩
    let b := B.max' hB
    have hb : b ∈ B := B.max'_mem hB
    have hbS : b ∈ S := (mem_filter.mp hb).1
    have hbsmall : b < a + u := (mem_filter.mp hb).2
    have hab : a ≤ b := S.min'_le _ hbS
    have hl : B ⊆ Icc a b := by
      intro s hs
      exact mem_Icc.mpr ⟨S.min'_le _ (mem_filter.mp hs).1, B.le_max' _ hs⟩
    have hbc : B.card ≤ b + 1 - a := by
      simpa using card_le_card hl
    have hBu : B.card ≤ u := by omega
    have hBb : B.card ≤ b + 1 := by omega
    let R := S \ B
    have hdisj : Disjoint R B := disjoint_left.mpr (fun s hs hsb => (mem_sdiff.mp hs).2 hsb)
    have hSsplit : R.card + B.card = S.card := by
      rw [← card_union_of_disjoint hdisj, sdiff_union_of_subset (filter_subset _ _)]
    rcases eq_empty_or_nonempty R with hR | hR
    · have hSB : S.card = B.card := by simpa [hR] using hSsplit.symm
      have hBN : B.card ≤ N := by have := hN b hbS; omega
      rw [hSB, add_mul, mul_add]
      calc
        u * B.card + v * B.card ≤ u * N + v * u := by gcongr
        _ = u * N + u * v := by rw [mul_comm v u]
    · let d := b + v + 1
      have hd : ∀ s ∈ R, d ≤ s := by
        intro s hs
        obtain ⟨hsS, hsB⟩ := mem_sdiff.mp hs
        have hlarge : a + u ≤ s := by
          by_contra! hh
          exact hsB (mem_filter.mpr ⟨hsS, hh⟩)
        have hfar := havoid a ha s hsS (by omega)
        have hfar' := havoid b hbS s hsS (by omega)
        dsimp [d]
        omega
      have hdN : d ≤ N := by
        obtain ⟨s, hs⟩ := hR
        exact (hd s hs).trans (hN s (mem_sdiff.mp hs).1).le
      let T := R.image (fun s => s - d)
      have hinj : Set.InjOn (fun s : ℕ => s - d) (↑R : Set ℕ) := by
        intro x hx y hy he
        change x - d = y - d at he
        have := hd x hx
        have := hd y hy
        omega
      have hcard : T.card = R.card := card_image_of_injOn hinj
      have hTN : ∀ s ∈ T, s < N - d := by
        intro s hs
        obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
        have := hd t ht
        have := hN t (mem_sdiff.mp ht).1
        omega
      have hTavoid : ∀ x ∈ T, ∀ y ∈ T, u ≤ y - x → v < y - x := by
        intro x hx y hy he
        obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
        have hxle := hd x' hx'
        have hyle := hd y' hy'
        have hf := havoid x' (mem_sdiff.mp hx').1 y' (mem_sdiff.mp hy').1 (by omega)
        omega
      have hRbound := ih (N - d) (by dsimp [d]; omega) T hTN hTavoid
      rw [hcard] at hRbound
      have hBbound : (u + v) * B.card ≤ u * d := calc
        _ = u * B.card + v * B.card := add_mul _ _ _
        _ ≤ u * (b + 1) + v * u := by gcongr
        _ = u * d := by dsimp [d]; ring
      rw [← hSsplit, mul_add]
      calc
        _ ≤ u * (N - d + v) + u * d := add_le_add hRbound hBbound
        _ = u * (N + v) := by
          rw [← mul_add]
          congr 1
          omega

