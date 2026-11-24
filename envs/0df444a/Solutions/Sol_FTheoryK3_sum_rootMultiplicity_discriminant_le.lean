-- Prove2me | solution 1 for FTheoryK3.sum_rootMultiplicity_discriminant_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T20:09:56.868197+00:00
-- url     : https://prove2.me/submissions/f58b7ea9-5584-4a67-8b5b-8589196e064e

import Definitions.Def_FTheoryK3Core

open Polynomial

variable {k : Type*} [Field k]

theorem solution (f g : k[X]) (h : FTheoryK3.Δ f g ≠ 0) (S : Finset k) :
    (∑ t₀ ∈ S, (FTheoryK3.Δ f g).rootMultiplicity t₀) ≤ (FTheoryK3.Δ f g).natDegree := by
  classical
  calc ∑ t₀ ∈ S, (FTheoryK3.Δ f g).rootMultiplicity t₀
      = ∑ t₀ ∈ S, (FTheoryK3.Δ f g).roots.count t₀ := by simp only [count_roots]
    _ ≤ ∑ t₀ ∈ S ∪ (FTheoryK3.Δ f g).roots.toFinset, (FTheoryK3.Δ f g).roots.count t₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun i _ _ => Nat.zero_le _)
    _ = (FTheoryK3.Δ f g).roots.card :=
        Multiset.sum_count_eq_card (fun a ha => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ (FTheoryK3.Δ f g).natDegree := card_roots' _

#check @solution
#print axioms solution
