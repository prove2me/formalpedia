-- Prove2me | solution 1 for EconomicsNextProof.alternating_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:15.973485+00:00
-- url     : https://prove2.me/submissions/51d8ded2-0c7a-4513-bc6c-65390b1ae934

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Mobius
section
@[expose] public section
namespace EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
omit [Fintype X] in
private lemma alternating_powerset (s : Finset X) :
    (∑ D ∈ s.powerset, (-1 : ℝ) ^ D.card) = if s = ∅ then 1 else 0 := by
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := s))
end EconomicsNextProof
end
end

set_option autoImplicit true
@[expose] public section
public section
open EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace EconomicsNextProof
theorem _root_.solution (A C : Finset X) (hAC : A ⊆ C) :
    (∑ B ∈ Finset.Icc A C, (-1 : ℝ) ^ (B \ A).card) = if A = C then 1 else 0 := by
  rw [Finset.Icc_eq_image_powerset hAC, Finset.sum_image]
  · have h : ∀ D ∈ (C \ A).powerset, (A ∪ D) \ A = D := by
      intro D hD
      have hDA := Finset.mem_powerset.mp hD
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · tauto
      · intro hx
        exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hDA hx)).2⟩
    calc
      ∑ D ∈ (C \ A).powerset, (-1 : ℝ) ^ ((A ∪ D) \ A).card
          = ∑ D ∈ (C \ A).powerset, (-1 : ℝ) ^ D.card := by
              exact Finset.sum_congr rfl (fun D hD => by rw [h D hD])
      _ = if A = C then 1 else 0 := by
        rw [alternating_powerset]
        congr 1
        exact propext ⟨fun h => Finset.Subset.antisymm hAC
          (Finset.sdiff_eq_empty_iff_subset.mp h), fun h => by simp [h]⟩

  · intro D hD E hE hEq
    have hDA := Finset.mem_powerset.mp hD
    have hEA := Finset.mem_powerset.mp hE
    ext x
    have hdx : x ∈ D → x ∉ A := fun hx => (Finset.mem_sdiff.mp (hDA hx)).2
    have hex : x ∈ E → x ∉ A := fun hx => (Finset.mem_sdiff.mp (hEA hx)).2
    have heq := Finset.ext_iff.mp hEq x
    simp only [Finset.mem_union] at heq
    tauto
end EconomicsNextProof
