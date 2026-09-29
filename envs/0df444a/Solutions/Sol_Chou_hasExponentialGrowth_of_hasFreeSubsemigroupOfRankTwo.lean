-- Prove2me | solution 1 for Chou.hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T15:28:55.85397+00:00
-- url     : https://prove2.me/submissions/d7c39e30-e665-44ef-8222-f16c1060ed21

import Definitions.Def_Chou_Growth
import Mathlib

/-! # Chou §3, p. 401: a free subsemigroup of rank two forces exponential growth -/

namespace Chou
namespace Lib

open Chou

variable {G : Type*} [Group G]

/-- The ball of radius `n` for a finite set `S` is finite: a nonempty word of length `≤ n + 1`
splits as a letter of `S ∪ S⁻¹` times a word of length `≤ n`. -/
lemma wordBall_finite (S : Finset G) (n : ℕ) : (wordBall (S : Set G) n).Finite := by
  classical
  induction n with
  | zero =>
      refine Set.Finite.subset (Set.finite_singleton (1 : G)) ?_
      rintro g ⟨l, hl, -, rfl⟩
      have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
      simp [hnil]
  | succ n ih =>
      have hT : ((↑(S ∪ S.image (fun y => y⁻¹)) : Set G)).Finite := Set.toFinite _
      refine Set.Finite.subset (Set.Finite.union (Set.finite_singleton (1 : G)) (hT.mul ih)) ?_
      rintro g ⟨l, hl, hmem, rfl⟩
      match l with
      | [] => exact Or.inl (by simp)
      | x :: t =>
          refine Or.inr ?_
          have hx : x ∈ ((↑(S ∪ S.image (fun y => y⁻¹)) : Set G)) := by
            have hx' := hmem x (by simp)
            simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
              Set.mem_image] at hx' ⊢
            rcases hx' with h | h
            · exact Or.inl (by simpa using h)
            · exact Or.inr ⟨x⁻¹, by simpa using h, by simp⟩
          have ht : t.prod ∈ wordBall (S : Set G) n :=
            ⟨t, by simpa using hl, fun y hy => hmem y (by simp [hy]), rfl⟩
          rw [List.prod_cons]
          exact Set.mul_mem_mul hx ht

/-- If `a, b` generate a free subsemigroup and both lie in `S`, the ball of radius `n` contains
the `2 ^ n` images of the words of length `n` in `a` and `b`. -/
lemma two_pow_le_card_wordBall {a b : G} (hab : Function.Injective (FreeMonoid.lift ![a, b]))
    (S : Finset G) (ha : a ∈ S) (hb : b ∈ S) (n : ℕ) :
    2 ^ n ≤ Nat.card (wordBall (S : Set G) n) := by
  classical
  have : Finite (wordBall (S : Set G) n) := (wordBall_finite S n).to_subtype
  have hmap : ∀ x : Fin n → Fin 2,
      FreeMonoid.lift ![a, b] (FreeMonoid.ofList (List.ofFn x)) ∈ wordBall (S : Set G) n := by
    intro x
    refine ⟨(List.ofFn x).map ![a, b], by simp, ?_, (FreeMonoid.lift_ofList _ _).symm⟩
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨i, -, rfl⟩ := hy
    refine Or.inl ?_
    fin_cases i
    · simpa using ha
    · simpa using hb
  set f : (Fin n → Fin 2) → wordBall (S : Set G) n := fun x => ⟨_, hmap x⟩ with hf_def
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : FreeMonoid.lift ![a, b] (FreeMonoid.ofList (List.ofFn x))
        = FreeMonoid.lift ![a, b] (FreeMonoid.ofList (List.ofFn y)) := congrArg Subtype.val hxy
    exact List.ofFn_injective (FreeMonoid.ofList.injective (hab h1))
  have hcard := Nat.card_le_card_of_injective f hf
  simpa using hcard

/-- p. 401: a finitely generated group containing a free subsemigroup on two generators has
exponential growth. -/
theorem hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo' {G : Type*} [Group G] [Group.FG G]
    (h : HasFreeSubsemigroupOfRankTwo G) : HasExponentialGrowth G := by
  classical
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨S₀, hS₀⟩ := Group.FG.out (G := G)
  refine ⟨insert a (insert b S₀), ?_, 2, by norm_num, ?_⟩
  · refine eq_top_iff.mpr ?_
    rw [← hS₀]
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx ⊢
    tauto
  · intro n
    have hn := two_pow_le_card_wordBall hab (insert a (insert b S₀)) (by simp) (by simp) n
    have : ((2 ^ n : ℕ) : ℝ) ≤ (Nat.card (wordBall ((insert a (insert b S₀) : Finset G) : Set G) n) : ℝ) :=
      Nat.cast_le.mpr hn
    simpa using this

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] [Group.FG G]
    (h : HasFreeSubsemigroupOfRankTwo G) : HasExponentialGrowth G :=
  Chou.Lib.hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo' h
