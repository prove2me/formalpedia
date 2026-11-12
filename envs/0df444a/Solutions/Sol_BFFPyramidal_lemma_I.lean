-- Prove2me | solution 1 for BFFPyramidal.lemma_I
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T18:51:42.637675+00:00
-- url     : https://prove2.me/submissions/c134734a-8060-41a3-a20a-0b7f5a793ff8

import Mathlib
open Pointwise

theorem solution {G : Type*} [Group G] (K L : Subgroup G) (a b : G) :
    (a • (K : Set G)) ∩ (b • (L : Set G)) = ∅ ∨
      ∃ c : G, (a • (K : Set G)) ∩ (b • (L : Set G)) = c • ((K ⊓ L : Subgroup G) : Set G) := by
  rcases Set.eq_empty_or_nonempty ((a • (K : Set G)) ∩ (b • (L : Set G))) with h | ⟨c, hc⟩
  · exact Or.inl h
  · refine Or.inr ⟨c, ?_⟩
    obtain ⟨hcK, hcL⟩ := hc
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hcK hcL
    ext x
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
      SetLike.mem_coe, Subgroup.mem_inf] at hcK hcL ⊢
    constructor
    · intro ⟨hxK, hxL⟩
      refine ⟨?_, ?_⟩
      · have : (a⁻¹ * c)⁻¹ * (a⁻¹ * x) ∈ K := K.mul_mem (K.inv_mem hcK) hxK
        simpa [mul_assoc] using this
      · have : (b⁻¹ * c)⁻¹ * (b⁻¹ * x) ∈ L := L.mul_mem (L.inv_mem hcL) hxL
        simpa [mul_assoc] using this
    · intro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : (a⁻¹ * c) * (c⁻¹ * x) ∈ K := K.mul_mem hcK h1
        simpa [mul_assoc] using this
      · have : (b⁻¹ * c) * (c⁻¹ * x) ∈ L := L.mul_mem hcL h2
        simpa [mul_assoc] using this

