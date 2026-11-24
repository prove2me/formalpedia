-- Prove2me | solution 1 for FairSelling.SEFXs_sellAll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:42.760672+00:00
-- url     : https://prove2.me/submissions/f985de4d-39ac-47ca-81b6-a415e33ea363

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Theorems.Thm_FairSelling_vbarSum_eq_sum_of_price_zero
import Theorems.Thm_FairSelling_price_zero_of_mem_bundle

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}
namespace FairSelling
theorem _root_.solution (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (hEFX : EFXalloc v A) :
    (sellAllOutcome sellable A (fun _ => 0)).Valid p ∧
      (sellAllOutcome sellable A (fun _ => 0)).AllocatesAll ∧
      SEFXs v p (sellAllOutcome sellable A (fun _ => 0)) := by
  classical
  have hpz : ∀ j, ∀ g ∈ A j, p g = 0 := fun j g hg => price_zero_of_mem_bundle hp0 hA j hg
  have hdisj : ∀ j, Disjoint sellable (A j) := by
    intro j
    refine Finset.disjoint_left.2 fun g hg hgA => ?_
    have : g ∈ Finset.univ \ sellable := by
      rw [← hA.2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hgA⟩
    exact (Finset.mem_sdiff.mp this).2 hg
  refine ⟨⟨hdisj, hA.1, fun _ => le_rfl, ?_⟩, ?_, ?_⟩
  · simp only [sellAllOutcome]
    simp only [Finset.sum_const_zero]
    exact Finset.sum_nonneg fun g _ => hp g
  · show sellable ∪ Finset.univ.biUnion A = Finset.univ
    rw [hA.2]
    simp
  · intro i j
    refine ⟨fun h => absurd h (by simp [sellAllOutcome]), fun g hg => ?_⟩
    have hgA : g ∈ A j := hg
    have h1 : vbarSum (v i) p (A i) = ∑ g' ∈ A i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g' hg' => hpz i g' hg')
    have h2 : vbarSum (v i) p (A j \ {g}) = ∑ g' ∈ A j \ {g}, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g)
        (fun g' hg' => hpz j g' (Finset.mem_sdiff.mp hg').1)
    have := hEFX i j g hgA
    simp only [sellAllOutcome, add_zero]
    rw [h1, h2, hpz j g hgA]
    simpa using this
end FairSelling
