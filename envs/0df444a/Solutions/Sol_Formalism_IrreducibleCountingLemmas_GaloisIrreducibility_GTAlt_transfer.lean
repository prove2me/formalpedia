-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GTAlt.transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:41.284057+00:00
-- url     : https://prove2.me/submissions/491c495f-06b3-40af-8de6-c02b5c6dd8b4

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G : Type} [Group G]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace GTAlt
theorem _root_.solution (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (u1 u2 : J) (g : G) (h : GTAlt σ J χ ((u1 : G) * g * u2)) : GTAlt σ J χ g := by
  rcases h with ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2⟩
  · left
    obtain ⟨m1, e1⟩ := hJ u1
    obtain ⟨m2, e2⟩ := hJ u2
    refine ⟨(⟨σ u2, m2⟩ : J)⁻¹ * a * u1, u2 * b * (⟨σ u1, m1⟩ : J)⁻¹, ?_, ?_⟩
    · rw [hσ, hσ] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : σ g = (σ u2)⁻¹ * (σ u2 * (σ g * σ u1)) * (σ u1)⁻¹ := by group
      rw [this, h1]
      group
    · simp only [map_mul, map_inv, e1, e2]
      calc (χ u2)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u1)⁻¹)
          = (χ a * χ b) * ((χ u2)⁻¹ * χ u2) * (χ u1 * (χ u1)⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = 1 := by rw [h2]; simp
  · right
    refine ⟨u1⁻¹ * a * u1, u2 * b * u2⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : (u1 : G)⁻¹ * a * u1 * g * (u2 * b * (u2 : G)⁻¹) =
          (u1 : G)⁻¹ * (a * (u1 * g * u2) * b) * (u2 : G)⁻¹ := by group
      rw [this, h1]
      group
    · simp only [map_mul, map_inv]
      intro h3
      apply h2
      calc χ a * χ b = (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) := by
            have : (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) =
              (χ a * χ b) * ((χ u1)⁻¹ * χ u1) * (χ u2 * (χ u2)⁻¹) := by
                simp only [mul_assoc, mul_comm, mul_left_comm]
            rw [this]; simp
        _ = 1 := h3
end GTAlt
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
