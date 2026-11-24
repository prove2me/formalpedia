-- Prove2me | solution 1 for FairSelling.exists_SEF1_of_exists_EF1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:49:58.370456+00:00
-- url     : https://prove2.me/submissions/2d187239-dafc-48ce-879e-75b935fd408c

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Theorems.Thm_FairSelling_vbarSum_eq_sum_of_price_zero
import Theorems.Thm_FairSelling_price_zero_of_mem_bundle
import Theorems.Thm_FairSelling_vbarSum_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}
namespace FairSelling
theorem _root_.solution (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hEF1 : ∃ A : Fin n → Finset G, IsPartitionOf A (Finset.univ \ sellable) ∧ EF1alloc v A) :
    ∃ o : Outcome G n, o.Valid p ∧ o.AllocatesAll ∧ SEF1 v p o := by
  classical
  obtain ⟨A, hA, hEF1⟩ := hEF1
  have hpz : ∀ j, ∀ g ∈ A j, p g = 0 := fun j g hg => price_zero_of_mem_bundle hp0 hA j hg
  have hdisj : ∀ j, Disjoint sellable (A j) := by
    intro j
    refine Finset.disjoint_left.2 fun g hg hgA => ?_
    have : g ∈ Finset.univ \ sellable := by
      rw [← hA.2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hgA⟩
    exact (Finset.mem_sdiff.mp this).2 hg
  refine ⟨sellAllOutcome sellable A (fun _ => 0), ⟨hdisj, hA.1, fun _ => le_rfl, ?_⟩, ?_, ?_⟩
  · simp only [sellAllOutcome, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun g _ => hp g
  · show sellable ∪ Finset.univ.biUnion A = Finset.univ
    rw [hA.2]; simp
  · intro i j
    refine ⟨fun h => absurd h (by simp [sellAllOutcome]), fun _ => ?_⟩
    rcases Finset.eq_empty_or_nonempty (A j) with hemp | hne
    · -- an empty envied bundle: the envy-free alternative holds
      refine Or.inl ?_
      have h1 : (0 : ℝ) ≤ vbarSum (v i) p (A i) := vbarSum_nonneg (hv i) _
      simp only [sellAllOutcome, hemp, vbarSum, Finset.sum_empty, add_zero, ge_iff_le]
      simpa [vbarSum] using h1
    refine Or.inr ?_
    obtain ⟨g, hgA, hx⟩ := hEF1 i j hne
    refine ⟨g, hgA, ?_⟩
    have h1 : vbarSum (v i) p (A i) = ∑ g' ∈ A i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g' hg' => hpz i g' hg')
    have h2 : vbarSum (v i) p (A j \ {g}) = ∑ g' ∈ A j \ {g}, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g)
        (fun g' hg' => hpz j g' (Finset.mem_sdiff.mp hg').1)
    simp only [sellAllOutcome]
    rw [h1, h2, hpz j g hgA]
    simpa using hx
end FairSelling
