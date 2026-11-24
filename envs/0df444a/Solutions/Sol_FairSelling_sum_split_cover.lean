-- Prove2me | solution 1 for FairSelling.sum_split_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:02.637931+00:00
-- url     : https://prove2.me/submissions/905941a9-3abf-4efe-bd67-81b70da3be80

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution {f : G → ℝ} (A R : Finset G) (Gb : Fin n → Finset G)
    (hcov : (Finset.univ : Finset G) = R ∪ Finset.univ.biUnion Gb)
    (hRG : ∀ b, Disjoint R (Gb b)) (hGG : ∀ b b', b ≠ b' → Disjoint (Gb b) (Gb b')) :
    ∑ g ∈ A, f g = (∑ g ∈ A ∩ R, f g) + ∑ b, ∑ g ∈ A ∩ Gb b, f g := by
  classical
  have h1 : A = (A ∩ R) ∪ (A ∩ Finset.univ.biUnion Gb) := by
    rw [← Finset.inter_union_distrib_left, ← hcov, Finset.inter_univ]
  have hdisj : Disjoint (A ∩ R) (A ∩ Finset.univ.biUnion Gb) := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx').2
    exact Finset.disjoint_left.mp (hRG b) (Finset.mem_inter.mp hx).2 hb
  have h2 : A ∩ Finset.univ.biUnion Gb = Finset.univ.biUnion (fun b => A ∩ Gb b) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxA, b, hb⟩; exact ⟨b, hxA, hb⟩
    · rintro ⟨b, hxA, hb⟩; exact ⟨hxA, b, hb⟩
  conv_lhs => rw [h1]
  rw [Finset.sum_union hdisj, h2, Finset.sum_biUnion]
  intro b _ b' _ hbb
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (hGG b b' hbb))
end FairSelling
