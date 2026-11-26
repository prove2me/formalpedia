-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:10:21.217356+00:00
-- url     : https://prove2.me/submissions/ca246a89-ce91-4743-9e1d-09b36fad607e

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_le_one
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_bad_bound
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
namespace IsCDDense
theorem _root_.solution
    {S T : Set ℕ} {C₁ C₂ D : ℝ}
    (hS : IsCDDense S C₁ D) (hT : IsCDDense T C₂ D) :
    IsCDDense (S ∩ T) (C₁ + C₂) D := by
  refine ⟨add_pos hS.C_pos hT.C_pos, hS.D_pos, hS.D_le_one, ?_⟩
  intro N hN
  have hsub :
      badPrefix (S ∩ T) N ⊆ badPrefix S N ∪ badPrefix T N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter, Finset.mem_union] at hn ⊢
    rcases hn with ⟨hnPrefix, hnInter⟩
    by_cases hnS : n ∈ S
    · exact Or.inr ⟨hnPrefix, fun hnT => hnInter ⟨hnS, hnT⟩⟩
    · exact Or.inl ⟨hnPrefix, hnS⟩
  have hcard :
      (badPrefix (S ∩ T) N).card ≤
        (badPrefix S N).card + (badPrefix T N).card :=
    le_trans (Finset.card_le_card hsub)
      (Finset.card_union_le (badPrefix S N) (badPrefix T N))
  have hcardReal :
      ((badPrefix (S ∩ T) N).card : ℝ) ≤
        (badPrefix S N).card + (badPrefix T N).card := by
    exact_mod_cast hcard
  calc
    ((badPrefix (S ∩ T) N).card : ℝ)
        ≤ (badPrefix S N).card + (badPrefix T N).card := hcardReal
    _ ≤ C₁ * (N : ℝ) ^ (1 - D) + C₂ * (N : ℝ) ^ (1 - D) :=
      add_le_add (hS.bad_bound N hN) (hT.bad_bound N hN)
    _ = (C₁ + C₂) * (N : ℝ) ^ (1 - D) := by ring
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
