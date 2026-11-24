-- Prove2me | solution 1 for FairSelling.servable_of_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:42.919807+00:00
-- url     : https://prove2.me/submissions/0b0b0df0-8ef2-4633-8a4b-5440daec22e1

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Theorems.Thm_FairSelling_servable_extend_set
import Theorems.Thm_FairSelling_Canonical_cash_nonneg
import Theorems.Thm_FairSelling_Canonical_sold_subset_sell
import Theorems.Thm_FairSelling_Canonical_sold_subset
import Theorems.Thm_FairSelling_round_outcome

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ} {μ : ℝ} {i : Fin n} (hi : i ∈ T)
    {k : ℕ} [NeZero k] (hk : T.card = k)
    (C : Canonical (v i) p μ (τ i) k R D)
    (hrec : ∀ (Kset : Finset (Fin n)) (part : Fin n → Fin k), i ∈ Kset → Kset ⊆ T →
        Set.InjOn part Kset →
        (∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
          vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < τ a) →
        (∀ a ∈ Kset, a ≠ i → part a ≠ 0) → (Kset = T ∨ part i ≠ 0) →
        Servable v p τ (T \ Kset)
          (R \ ((Kset.image part).biUnion C.goods ∪ C.sold (Kset.image part)))
          (D + (∑ g ∈ C.sold (Kset.image part), p g)
              - ∑ j ∈ Kset.image part, C.cash j)) :
    Servable v p τ T R D := by
  classical
  obtain ⟨Kset, part, hiK, hKT, hinj, hserve, hloss, hspecial, hzero⟩ :=
    round_outcome v p τ hi hk C
  have himage : Kset.biUnion (fun a => C.goods (part a)) = (Kset.image part).biUnion C.goods := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hg⟩; exact ⟨part a, ⟨a, ha, rfl⟩, hg⟩
    · rintro ⟨j, ⟨a, ha, rfl⟩, hg⟩; exact ⟨a, ha, hg⟩
  have hsum : ∑ a ∈ Kset, C.cash (part a) = ∑ j ∈ Kset.image part, C.cash j :=
    (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
  refine servable_extend_set v p τ Kset hKT (fun a => C.goods (part a))
    (C.sold (Kset.image part)) (fun a => C.cash (part a))
    (fun a _ => C.goods_subset _) (C.sold_subset _) ?_ ?_
    (fun a _ => C.cash_nonneg _) hserve ?_
  · intro a ha b hb hab
    exact C.goods_disj _ _ (fun h => hab (hinj ha hb h))
  · intro a _
    exact Finset.disjoint_of_subset_left (C.sold_subset_sell _) (C.sell_disj _)
  · rw [himage, hsum]
    exact hrec Kset part hiK hKT hinj hloss hspecial hzero
end FairSelling
