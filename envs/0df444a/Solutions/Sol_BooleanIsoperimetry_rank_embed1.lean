-- Prove2me | solution 1 for BooleanIsoperimetry.rank_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:44.437915+00:00
-- url     : https://prove2.me/submissions/00b20d6c-0b65-4f64-8a06-3bcbd657148f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_card_filter_card_lt
public import Theorems.Thm_BooleanIsoperimetry_simplicialLt_embed1_embed1
public import Theorems.Thm_BooleanIsoperimetry_simplicialLt_embed0_embed1
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (w : Cube n) :
    rank (embed1 w) = rank w + binomPrefix n (w.card + 1) := by
  classical
  unfold rank
  have h_partition : Finset.univ.filter (fun v : Cube (n + 1) => simplicialLt v (embed1 w)) =
      (Finset.univ.filter (fun u : Cube n => simplicialLt (embed0 u) (embed1 w))).image embed0 ∪
      (Finset.univ.filter (fun u : Cube n => simplicialLt (embed1 u) (embed1 w))).image embed1 := by
    ext v
    simp [Finset.mem_image, Finset.mem_union]
    by_cases hv : Fin.last n ∈ v
    · -- Since `Fin.last n ∈ v`, we can write `v` as `embed1 u` for some `u : Cube n`.
      obtain ⟨u, hu⟩ : ∃ u : Cube n, v = embed1 u := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ v)
        ext i; simp [embed1]
        induction i using Fin.lastCases <;> aesop
      grind
    · -- Since $Fin.last n \notin v$, we can write $v$ as $embed0 u$ for some $u \in Cube n$.
      obtain ⟨u, hu⟩ : ∃ u : Cube n, v = embed0 u := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ v)
        ext i; simp [embed0]
        induction i using Fin.lastCases <;> aesop
      grind
  rw [h_partition, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective, Finset.card_image_of_injective]
    · rw [show (Finset.univ.filter fun u : Cube n => simplicialLt (embed0 u) (embed1 w)) =
          Finset.univ.filter fun u : Cube n => u.card < w.card + 1 from ?_,
        show (Finset.univ.filter fun u : Cube n => simplicialLt (embed1 u) (embed1 w)) =
          Finset.univ.filter fun u : Cube n => simplicialLt u w from ?_]
      · rw [add_comm, card_filter_card_lt]
      · ext u; simp [simplicialLt_embed1_embed1]
      · ext u; simp [simplicialLt_embed0_embed1]
    · intro x y; simp +decide only [embed1]
      intro h; ext i; replace h := Finset.ext_iff.mp h (Fin.castSucc i) ; aesop
    · intro x y; simp +decide only [embed0]
      exact fun h => Finset.image_injective (Fin.castSucc_injective _) h
  · norm_num [Finset.disjoint_left, embed0, embed1]
    intro a ha x hx H; replace H := Finset.ext_iff.mp H (Fin.last n) ; aesop
end BooleanIsoperimetry
