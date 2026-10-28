-- Prove2me | solution 1 for Erdos624.prescribed_core_cover
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:41:11.57497+00:00
-- url     : https://prove2.me/submissions/7dad54f5-d59c-429a-a419-8eec4e62c424

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624R5
open Finset

/-- Every prescribed `(k-2)`-core can be defeated: two maps jointly cover `U` on every
`k`-set containing `W`. -/
theorem prescribed_core_cover (k : ℕ) (hk : 3 ≤ k) (W : Finset (Fin (2 ^ k)))
    (hW : #W = k - 2) :
    ∃ g : Fin 2 → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
      ∀ Y : Finset (Fin (2 ^ k)), #Y = k → W ⊆ Y → ∀ u, ∃ i, ∃ A ⊆ Y, g i A = u := by
  have hcard : Fintype.card (Fin 2 × Bool × Finset W) = Fintype.card (Fin (2 ^ k)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_finset,
      Fintype.card_coe, hW]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]; ring
  let θ := Fintype.equivOfCardEq hcard
  refine ⟨fun i A => θ (i, !decide (A ⊆ W), A.subtype (· ∈ W)), ?_⟩
  intro Y hY hWY u
  have hu : u = θ (θ.symm u) := (θ.apply_symm_apply u).symm
  obtain ⟨⟨i, e, B⟩, hp⟩ : ∃ p, θ.symm u = p := ⟨_, rfl⟩
  rw [hp] at hu
  set B' : Finset (Fin (2 ^ k)) := B.map (Function.Embedding.subtype _) with hB'
  have hB'W : B' ⊆ W := by
    intro x hx; rw [hB', mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact y.2
  have hsubB : ∀ a, a ∉ W → (insert a B').subtype (· ∈ W) = B := by
    intro a ha; ext y
    simp only [mem_subtype, mem_insert, hB', mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro (h | ⟨z, hz, hzy⟩)
      · exact absurd (h ▸ y.2) ha
      · rwa [← Subtype.ext hzy]
    · intro hy; exact Or.inr ⟨y, hy, rfl⟩
  have hsubB0 : B'.subtype (· ∈ W) = B := by
    ext y
    simp only [mem_subtype, hB', mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨z, hz, hzy⟩; rwa [← Subtype.ext hzy]
    · intro hy; exact ⟨y, hy, rfl⟩
  refine ⟨i, ?_⟩
  cases e with
  | false =>
    refine ⟨B', hB'W.trans hWY, ?_⟩
    rw [hu]; simp only [hB'W, decide_true, Bool.not_true, hsubB0]
  | true =>
    obtain ⟨a, haY, haW⟩ : ∃ a ∈ Y, a ∉ W := by
      by_contra hc; push Not at hc
      have := card_le_card (show Y ⊆ W from hc)
      omega
    refine ⟨insert a B', insert_subset haY (hB'W.trans hWY), ?_⟩
    have hnot : ¬ insert a B' ⊆ W := fun h => haW (h (mem_insert_self _ _))
    rw [hu]; simp only [hnot, decide_false, Bool.not_false, hsubB a haW]


/-- Collision identity (1): with `C(Y) = 2·2^k − |J(Y)|` evaluations wasted, `C(Y) = n + (n − |J(Y)|)`,
and a common hole exists iff `C(Y) > n`. -/
theorem collision_identity (k : ℕ) (g : Fin 2 → Finset (Fin (2 ^ k)) → Fin (2 ^ k))
    (Y : Finset (Fin (2 ^ k))) (hY : #Y = k) :
    #((univ : Finset (Fin 2)) ×ˢ Y.powerset) -
        #(((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2)) =
      2 ^ k + (2 ^ k - #(((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2))) ∧
    ((∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u) ↔
      2 ^ k < #((univ : Finset (Fin 2)) ×ˢ Y.powerset) -
        #(((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2))) := by
  set J := ((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2) with hJ
  have hT : #((univ : Finset (Fin 2)) ×ˢ Y.powerset) = 2 * 2 ^ k := by
    rw [card_product, card_powerset, hY, card_univ, Fintype.card_fin]
  have hJle : #J ≤ 2 ^ k := by
    have := card_le_univ J; rwa [Fintype.card_fin] at this
  refine ⟨by omega, ?_⟩
  rw [hT]
  constructor
  · rintro ⟨u, hu⟩
    have : J ≠ univ := by
      intro he
      have : u ∈ J := by rw [he]; exact mem_univ _
      obtain ⟨⟨i, A⟩, hp, he⟩ := mem_image.1 this
      rw [mem_product, mem_powerset] at hp
      exact hu i A hp.2 he
    have hlt : #J < 2 ^ k := by
      by_contra hc
      apply this; apply eq_univ_of_card; rw [Fintype.card_fin]; omega
    omega
  · intro h
    have hlt : #J < 2 ^ k := by omega
    obtain ⟨u, hu⟩ : ∃ u, u ∉ J := by
      by_contra hc; push Not at hc
      have : J = univ := eq_univ_of_forall hc
      rw [this, card_univ, Fintype.card_fin] at hlt; omega
    exact ⟨u, fun i A hA he => hu (mem_image.2 ⟨(i, A), mem_product.2 ⟨mem_univ _, mem_powerset.2 hA⟩, he⟩)⟩

/-- Rank-only maps (8): if each map depends only on `|A|`, the joint image has at most
`r(|Y|+1)` points. -/
theorem rank_only_bound {U : Type*} [DecidableEq U] (r : ℕ) (h : Fin r → ℕ → U)
    (Y : Finset U) :
    #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => h p.1 (#p.2))) ≤ r * (#Y + 1) := by
  have hsub : ((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => h p.1 (#p.2)) ⊆
      ((univ : Finset (Fin r)) ×ˢ range (#Y + 1)).image (fun p => h p.1 p.2) := by
    intro b hb
    obtain ⟨⟨i, A⟩, hp, rfl⟩ := mem_image.1 hb
    rw [mem_product, mem_powerset] at hp
    exact mem_image.2 ⟨(i, #A), mem_product.2 ⟨mem_univ _,
      mem_range.2 (Nat.lt_succ_of_le (card_le_card hp.2))⟩, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ #((univ : Finset (Fin r)) ×ˢ range (#Y + 1)) := card_image_le
    _ = r * (#Y + 1) := by rw [card_product, card_range, card_univ, Fintype.card_fin]

end E624R5


namespace Erdos624

theorem prescribed_core_cover (k : ℕ) (hk : 3 ≤ k) (W : Finset (Fin (2 ^ k)))
    (hW : #W = k - 2) :
    ∃ g : Fin 2 → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
      ∀ Y : Finset (Fin (2 ^ k)), #Y = k → W ⊆ Y → ∀ u, ∃ i, ∃ A ⊆ Y, g i A = u :=
  E624R5.prescribed_core_cover k hk W hW

end Erdos624

open Erdos624 in
theorem solution (k : ℕ) (hk : 3 ≤ k) (W : Finset (Fin (2 ^ k)))
    (hW : #W = k - 2) :
    ∃ g : Fin 2 → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
      ∀ Y : Finset (Fin (2 ^ k)), #Y = k → W ⊆ Y → ∀ u, ∃ i, ∃ A ⊆ Y, g i A = u :=
  Erdos624.prescribed_core_cover k hk W hW

#print axioms solution
