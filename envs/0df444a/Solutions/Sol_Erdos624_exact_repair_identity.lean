-- Prove2me | solution 1 for Erdos624.exact_repair_identity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:42.037015+00:00
-- url     : https://prove2.me/submissions/9bffd385-3f25-4e0e-bd22-1e1d0c4fb5b0

import Mathlib

namespace Erdos624

open Finset

/-- Key pointwise fact: colour `u` disappears from the palette when `y` is deleted from `Y`
iff `y` lies in every witness `A ⊆ Y` of `u`. -/
lemma repair_not_mem_erase_iff {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (Y : Finset U) (y : U) (u : C) :
    u ∉ (Y.erase y).powerset.biUnion L ↔
      y ∈ (Y.powerset.filter (fun A => u ∈ L A)).inf id := by
  rw [Finset.mem_inf]
  simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_filter, id, not_exists, not_and]
  constructor
  · intro h A ⟨hAY, huA⟩
    by_contra hy
    exact h A (fun x hx => Finset.mem_erase.2 ⟨fun hxy => hy (hxy ▸ hx), hAY hx⟩) huA
  · intro h A hA huA
    have := h A ⟨fun x hx => Finset.mem_of_mem_erase (hA hx), huA⟩
    exact (Finset.notMem_erase y A) (by simpa using hA this)

/-- Per-face repair identity. -/
lemma repair_face {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (Y B : Finset U) :
    ∑ y ∈ Y \ B, (Fintype.card C - ((Y.erase y).powerset.biUnion L).card)
      = (Y \ B).card * (Fintype.card C - (Y.powerset.biUnion L).card)
        + ∑ u ∈ Y.powerset.biUnion L,
            (((Y.powerset.filter (fun A => u ∈ L A)).inf id) \ B).card := by
  set c := Fintype.card C
  set JY := Y.powerset.biUnion L
  have hJc : JY.card ≤ c := Finset.card_le_univ _
  have hsub : ∀ y, (Y.erase y).powerset.biUnion L ⊆ JY := by
    intro y
    apply Finset.biUnion_subset_biUnion_of_subset_left
    exact Finset.powerset_mono.2 (Finset.erase_subset y Y)
  -- step 1: split each deficit
  have step1 : ∀ y, c - ((Y.erase y).powerset.biUnion L).card
      = (c - JY.card) + (JY \ (Y.erase y).powerset.biUnion L).card := by
    intro y
    rw [Finset.card_sdiff_of_subset (hsub y)]
    have := Finset.card_le_card (hsub y)
    omega
  rw [Finset.sum_congr rfl (fun y _ => step1 y), Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul]
  congr 1
  -- step 2: swap sums
  have step2 : ∀ y, (JY \ (Y.erase y).powerset.biUnion L).card
      = ∑ u ∈ JY, if y ∈ (Y.powerset.filter (fun A => u ∈ L A)).inf id then 1 else 0 := by
    intro y
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    rw [repair_not_mem_erase_iff]
  rw [Finset.sum_congr rfl (fun y _ => step2 y), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_boole, Nat.cast_id]
  congr 1
  -- E_u(Y) ⊆ Y because u has a witness inside Y
  have hEY : (Y.powerset.filter (fun A => u ∈ L A)).inf id ⊆ Y := by
    obtain ⟨A, hA, huA⟩ := Finset.mem_biUnion.1 hu
    have hAmem : A ∈ Y.powerset.filter (fun A => u ∈ L A) := Finset.mem_filter.2 ⟨hA, huA⟩
    exact (Finset.inf_le (f := id) hAmem).trans (Finset.mem_powerset.1 hA)
  ext y
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨_, hyB⟩, hyE⟩; exact ⟨hyE, hyB⟩
  · rintro ⟨hyE, hyB⟩; exact ⟨⟨hEY hyE, hyB⟩, hyE⟩

/-- Double counting of pairs (W, y) with W a (j-1)-face containing B and y ∈ V \ W. -/
lemma repair_double_count {U : Type*} [DecidableEq U] (V B : Finset U) (j : ℕ) (hj : 1 ≤ j)
    (f : Finset U → ℕ) :
    ∑ W ∈ (V.powersetCard (j - 1)).filter (fun W => B ⊆ W), (V.card + 1 - j) * f W
      = ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y), ∑ y ∈ Y \ B, f (Y.erase y) := by
  have hcard : ∀ W ∈ (V.powersetCard (j - 1)).filter (fun W => B ⊆ W),
      (V.card + 1 - j) * f W = ∑ _y ∈ V \ W, f W := by
    intro W hW
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hW
    rw [Finset.sum_const, smul_eq_mul, Finset.card_sdiff_of_subset hW.1.1, hW.1.2]
    congr 1
    omega
  rw [Finset.sum_congr rfl hcard, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨insert p.2 p.1, p.2⟩) (fun p _ => ⟨p.1.erase p.2, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨W, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_sdiff] at hp ⊢
    obtain ⟨⟨⟨hWV, hWc⟩, hBW⟩, hyV, hyW⟩ := hp
    refine ⟨⟨⟨Finset.insert_subset hyV hWV, ?_⟩, hBW.trans (Finset.subset_insert _ _)⟩,
      Finset.mem_insert_self _ _, fun hyB => hyW (hBW hyB)⟩
    rw [Finset.card_insert_of_notMem hyW, hWc]; omega
  · rintro ⟨Y, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_sdiff] at hp ⊢
    obtain ⟨⟨⟨hYV, hYc⟩, hBY⟩, hyY, hyB⟩ := hp
    refine ⟨⟨⟨(Finset.erase_subset _ _).trans hYV, ?_⟩, ?_⟩, hYV hyY, Finset.notMem_erase _ _⟩
    · rw [Finset.card_erase_of_mem hyY, hYc]
    · intro x hx
      exact Finset.mem_erase.2 ⟨fun hxy => hyB (hxy ▸ hx), hBY hx⟩
  · rintro ⟨W, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_sdiff] at hp
    simp [Finset.erase_insert hp.2.2]
  · rintro ⟨Y, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_sdiff] at hp
    simp [Finset.insert_erase hp.2.1]
  · rintro ⟨W, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_sdiff] at hp
    simp [Finset.erase_insert hp.2.2]

/-- **Exact repair identity** (Round 10, Sol consolidated report). For any list system
`L : Finset U → Finset C` (in particular `L A = {g₀ A, g₁ A}`), with
`J(Y) = ⋃_{A ⊆ Y} L(A)`, `D(Y) = |C| - |J(Y)|`, `E_u(Y) = ⋂ {A ⊆ Y : u ∈ L A}`:
`(N - j + 1) Σ_{W ⊇ B, |W| = j-1} D(W) = (j - b) Σ_{Y ⊇ B, |Y| = j} D(Y)
   + Σ_{Y} Σ_{u ∈ J(Y)} |E_u(Y) \ B|`. -/
theorem exact_repair_identity {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C]
    [DecidableEq C] (L : Finset U → Finset C) (V B : Finset U) (j : ℕ) (hj : B.card < j) :
    (V.card + 1 - j) * ∑ W ∈ (V.powersetCard (j - 1)).filter (fun W => B ⊆ W),
        (Fintype.card C - (W.powerset.biUnion L).card)
      = (j - B.card) * ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y),
          (Fintype.card C - (Y.powerset.biUnion L).card)
        + ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y),
            ∑ u ∈ Y.powerset.biUnion L,
              (((Y.powerset.filter (fun A => u ∈ L A)).inf id) \ B).card := by
  rw [Finset.mul_sum, repair_double_count V B j (by omega)
    (fun W => Fintype.card C - (W.powerset.biUnion L).card), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Y hY
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hY
  rw [repair_face L Y B, Finset.card_sdiff_of_subset hY.2, hY.1.2]

end Erdos624

open Finset

theorem solution {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C]
    [DecidableEq C] (L : Finset U → Finset C) (V B : Finset U) (j : ℕ) (hj : B.card < j) :
    (V.card + 1 - j) * ∑ W ∈ (V.powersetCard (j - 1)).filter (fun W => B ⊆ W),
        (Fintype.card C - (W.powerset.biUnion L).card)
      = (j - B.card) * ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y),
          (Fintype.card C - (Y.powerset.biUnion L).card)
        + ∑ Y ∈ (V.powersetCard j).filter (fun Y => B ⊆ Y),
            ∑ u ∈ Y.powerset.biUnion L,
              (((Y.powerset.filter (fun A => u ∈ L A)).inf id) \ B).card :=
  Erdos624.exact_repair_identity L V B j hj
