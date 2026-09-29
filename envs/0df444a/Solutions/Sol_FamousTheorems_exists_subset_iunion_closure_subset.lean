-- Prove2me | solution 1 for FamousTheorems.exists_subset_iunion_closure_subset
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:54:57.073226+00:00
-- url     : https://prove2.me/submissions/b93264d3-f38e-4fc9-92ad-953b824db3d7

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} {X : Type u_2} [inst : TopologicalSpace X] {u : ι → Set X} 
    {s : Set X} [NormalSpace X], 
    IsClosed s → 
    (∀ (i : ι), IsOpen (u i)) → 
    (∀ x ∈ s, {i | x ∈ u i}.Finite) → 
    s ⊆ ⋃ i, u i → ∃ v, s ⊆ iUnion v ∧ (∀ (i : ι), IsOpen (v i)) ∧ ∀ (i : ι), closure (v i) ⊆ u i :=
  @_root_.exists_subset_iUnion_closure_subset
