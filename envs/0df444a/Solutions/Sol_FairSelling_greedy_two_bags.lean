-- Prove2me | solution 1 for FairSelling.greedy_two_bags
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:23.931935+00:00
-- url     : https://prove2.me/submissions/af2076fe-057b-4cd6-9b17-4124d0fa60a6

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
import Theorems.Thm_FairSelling_bagfill
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (u : G → ℝ) (hu : ∀ g, 0 ≤ u g)
    (τ : ℝ) (hτ : 0 < τ) (S : Finset G)
    (hsmall : ∀ g ∈ S, u g < (2/3) * τ)
    (htot : 3 * τ ≤ ∑ g ∈ S, u g) :
    ∃ B1 B2 : Finset G, B1 ⊆ S ∧ B2 ⊆ S ∧ Disjoint B1 B2 ∧
      τ ≤ ∑ g ∈ B1, u g ∧ τ ≤ ∑ g ∈ B2, u g ∧
      (∑ g ∈ B1, u g) + (∑ g ∈ B2, u g) ≤ 3 * τ := by
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ ∈ S, ∀ x ∈ S, u x ≤ u x₁ := by
    exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty ( by rintro rfl; norm_num at htot; linarith ) );
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ ∈ S \ {x₁}, ∀ x ∈ S \ {x₁}, u x ≤ u x₂ := by
    by_cases hS_singleton : S = {x₁};
    · grind;
    · exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty ( by aesop ) );
  by_cases h_case : τ ≤ u x₁ + u x₂;
  · refine' ⟨ { x₁, x₂ }, _ ⟩;
    have := bagfill u τ ( ( 5 / 3 ) * τ ) ( by linarith ) ( by linarith ) ( S \ { x₁, x₂ } ) ?_ ?_ <;> simp_all +decide [ Finset.subset_iff ]; all_goals grind;
  · -- Apply `bagfill` to `S \ {x₁}` with `lo = τ - u x₁` and `hi = τ - u x₁ + τ/2`.
    obtain ⟨B1', hB1'⟩ : ∃ B1' ⊆ S \ {x₁}, τ - u x₁ ≤ ∑ g ∈ B1', u g ∧ ∑ g ∈ B1', u g ≤ τ - u x₁ + τ / 2 := by
      apply bagfill;
      · linarith [ hu x₁, hu x₂, hsmall x₁ hx₁.1, hsmall x₂ ( Finset.mem_sdiff.mp hx₂.1 |>.1 ) ];
      · linarith;
      · grind +qlia;
      · rw [ ← Finset.add_sum_erase _ _ hx₁.1, Finset.erase_eq ] at htot ; linarith [ hu x₁ ];
    -- Apply `bagfill` to `S \ B1` with `lo = τ` and `hi = (3/2)τ`.
    obtain ⟨B2, hB2⟩ : ∃ B2 ⊆ S \ (insert x₁ B1'), τ ≤ ∑ g ∈ B2, u g ∧ ∑ g ∈ B2, u g ≤ (3 / 2) * τ := by
      apply bagfill;
      · linarith;
      · linarith;
      · grind;
      · rw [ ← Finset.sum_sdiff ( show insert x₁ B1' ⊆ S from ?_ ) ] at *;
        · grind;
        · exact Finset.insert_subset hx₁.1 ( Finset.Subset.trans hB1'.1 ( Finset.sdiff_subset ) );
    refine' ⟨ insert x₁ B1', B2, _, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact ⟨ fun hx => hB2.1 hx |>.2.1 rfl, Finset.disjoint_left.mpr fun x hx₁ hx₂ => hB2.1 hx₂ |>.2.2 hx₁ ⟩;
    · grind;
    · grind
end FairSelling
