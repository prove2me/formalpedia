-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.mono_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:10:10.973351+00:00
-- url     : https://prove2.me/submissions/5797fdda-8058-48d8-b034-dd0ba1ce6bf9

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
    {S T : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) (hST : S ⊆ T) :
    IsCDDense T C D := by
  refine ⟨h.C_pos, h.D_pos, h.D_le_one, ?_⟩
  intro N hN
  have hsub : badPrefix T N ⊆ badPrefix S N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hnS => hn.2 (hST hnS)⟩
  have hcard : (badPrefix T N).card ≤ (badPrefix S N).card :=
    Finset.card_le_card hsub
  calc
    ((badPrefix T N).card : ℝ) ≤ ((badPrefix S N).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ C * (N : ℝ) ^ (1 - D) := h.bad_bound N hN
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
