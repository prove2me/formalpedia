-- Prove2me | solution 1 for FamousTheorems.compactspace_of_closed_inducing
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:05.354254+00:00
-- url     : https://prove2.me/submissions/bfe45207-f5e3-467e-9c40-91dd04ccef1c

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} {X : Type u_2} {α : Type u_3} 
    [inst : TopologicalSpace X] [inst_1 : UniformSpace α] {F : ι → X → α} [inst_2 : TopologicalSpace ι] {𝔖 : Set (Set X)}, 
    (∀ K ∈ 𝔖, IsCompact K) → 
    IsInducing (⇑(UniformOnFun.ofFun 𝔖) ∘ F) → 
    IsClosed (range (⇑(UniformOnFun.ofFun 𝔖) ∘ F)) → 
    (∀ K ∈ 𝔖, EquicontinuousOn F K) → (∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ (i : ι), F i x ∈ Q) → CompactSpace ι :=
  @_root_.ArzelaAscoli.compactSpace_of_closed_inducing'
