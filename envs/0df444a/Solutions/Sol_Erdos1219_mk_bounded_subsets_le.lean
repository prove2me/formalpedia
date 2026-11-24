-- Prove2me | solution 1 for Erdos1219.mk_bounded_subsets_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:40.65591+00:00
-- url     : https://prove2.me/submissions/38ec5828-6ff6-4647-8780-dd6335ad0b68

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Theorems.Thm_Erdos1219_two_pow_pow_self
import Theorems.Thm_Erdos1219_aleph0_le_two_pow

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V : Type u} (U : Set V) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hU : #U ≤ 2 ^ μ) : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ 2 ^ μ := by
  have key : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ #{t : Set (↥U) // #t ≤ μ} := by
    refine mk_le_of_injective (f := fun B => ⟨Subtype.val ⁻¹' B.1, ?_⟩) ?_
    · rw [mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective
        (by simpa using B.2.1)]
      exact B.2.2
    · rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
      simp only [Subtype.mk.injEq] at h
      have h1 : ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B) = B :=
        Set.image_preimage_eq_of_subset (by simpa using hB.1)
      have h2 : ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B') = B' :=
        Set.image_preimage_eq_of_subset (by simpa using hB'.1)
      rw [Subtype.mk.injEq]
      calc B = ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B) := h1.symm
        _ = ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B') := by rw [h]
        _ = B' := h2
  refine key.trans ((mk_bounded_set_le (↥U) μ).trans ?_)
  have hmax : max #U ℵ₀ ≤ 2 ^ μ := max_le hU (aleph0_le_two_pow hμ)
  exact (power_le_power_right hmax).trans (two_pow_pow_self hμ).le
end Erdos1219
