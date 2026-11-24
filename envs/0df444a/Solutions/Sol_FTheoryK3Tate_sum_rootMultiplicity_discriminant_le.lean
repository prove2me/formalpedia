-- Prove2me | solution 1 for FTheoryK3Tate.sum_rootMultiplicity_discriminant_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T11:08:55.549433+00:00
-- url     : https://prove2.me/submissions/a7cd7ad9-23ec-4560-9389-d919a4e963c5

import Definitions.Def_FTheoryK3TateCore

open Polynomial

open FTheoryK3Tate

variable {k : Type*} [Field k]

theorem solution (f g : k[X]) (_h : Δ f g ≠ 0) (S : Finset k) :
    (∑ t₀ ∈ S, (Δ f g).rootMultiplicity t₀) ≤ (Δ f g).natDegree := by
  classical
  calc ∑ t₀ ∈ S, (Δ f g).rootMultiplicity t₀
      = ∑ t₀ ∈ S, (Δ f g).roots.count t₀ := by simp only [count_roots]
    _ ≤ ∑ t₀ ∈ S ∪ (Δ f g).roots.toFinset, (Δ f g).roots.count t₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun i _ _ => Nat.zero_le _)
    _ = (Δ f g).roots.card :=
        Multiset.sum_count_eq_card (fun a ha => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ (Δ f g).natDegree := card_roots' _

#check @solution
#print axioms solution
