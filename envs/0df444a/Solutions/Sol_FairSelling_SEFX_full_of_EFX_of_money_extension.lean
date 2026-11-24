-- Prove2me | solution 1 for FairSelling.SEFX_full_of_EFX_of_money_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:02.502979+00:00
-- url     : https://prove2.me/submissions/db6541f0-2ad2-419d-bf01-f27fa360a301

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
theorem _root_.solution (hv : ∀ i g, 0 ≤ v i g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (hEFX : EFXalloc v A)
    (hext : ∃ P : Fin n → ℝ, (∀ j, 0 ≤ P j) ∧ (∑ j, P j = ∑ g ∈ sellable, p g) ∧
      ∀ i j, 0 < P j → (∑ g' ∈ A i, v i g') + P i ≥ (∑ g' ∈ A j, v i g') + P j) :
    ∃ o : Outcome G n, o.Full p sellable ∧ SEFX v p o := by
  classical
  obtain ⟨P, hP0, hPsum, hPEF⟩ := hext
  have hpz : ∀ j, ∀ g ∈ A j, p g = 0 := fun j g hg => price_zero_of_mem_bundle hp0 hA j hg
  have hbar : ∀ i j, vbarSum (v i) p (A j) = ∑ g' ∈ A j, v i g' := fun i j =>
    vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g' hg' => hpz j g' hg')
  have hdisj : ∀ j, Disjoint sellable (A j) := by
    intro j
    refine Finset.disjoint_left.2 fun g hg hgA => ?_
    have : g ∈ Finset.univ \ sellable := by
      rw [← hA.2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hgA⟩
    exact (Finset.mem_sdiff.mp this).2 hg
  refine ⟨sellAllOutcome sellable A P, ⟨⟨hdisj, hA.1, hP0, le_of_eq hPsum⟩, Finset.Subset.refl _,
    ?_, hPsum⟩, ?_⟩
  · show sellable ∪ Finset.univ.biUnion A = Finset.univ
    rw [hA.2]; simp
  · intro i j
    refine ⟨fun hj => ?_, fun hj => Or.inr fun g hg => ?_⟩
    · have := hPEF i j hj
      simp only [sellAllOutcome, hbar]
      exact this
    · have hgA : g ∈ A j := hg
      have hPi : (0 : ℝ) ≤ P i := hP0 i
      have h2 : vbarSum (v i) p (A j \ {g}) = ∑ g' ∈ A j \ {g}, v i g' :=
        vbarSum_eq_sum_of_price_zero (fun g => hv i g)
          (fun g' hg' => hpz j g' (Finset.mem_sdiff.mp hg').1)
      have := hEFX i j g hgA
      simp only [sellAllOutcome, hbar, h2, hpz j g hgA, add_zero]
      linarith
end FairSelling
