-- Prove2me | solution 1 for Formalism.QuantumDeterminants.symmetric_group_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:31:35.840039+00:00
-- url     : https://prove2.me/submissions/f1f0b446-a08b-4f6d-9ed9-a4fbfe8d6502

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one
import Theorems.Thm_Formalism_QuantumDeterminants_unipotent_subgroup_holds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_mul
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_weyl_normal_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WeylGroupFacts
namespace Formalism.QuantumDeterminants
theorem _root_.solution : SGroup := by
  unfold SGroup
  intro k r z hz
  have hN := unipotent_subgroup_holds k r
  have hW := unitary_weyl_normal_holds k r z hz
  have hW1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
    simp only [UWset, Set.mem_setOf_eq]
    exact ⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨⟨1, hW1, 1, hN.1, (mul_one 1).symm⟩, ?_, ?_⟩
  · rintro s ⟨h, hh, m, hm, rfl⟩ t ⟨h', hh', m', hm', rfl⟩
    have hU' : h' ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh'
      exact hh'.1
    have hd' := isUnit_of_uh hU'
    have hc := (hW h'⁻¹ (uw_inv hh') m hm).1
    rw [Matrix.nonsing_inv_nonsing_inv h' hd'] at hc
    refine ⟨h * h', uw_mul hh hh', h'⁻¹ * m * h' * m', hN.2.1 _ hc _ hm', ?_⟩
    calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
          rw [Matrix.mul_nonsing_inv h' hd', mul_one]
          simp only [mul_assoc]
      _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [mul_assoc]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hd := isUnit_of_uh hU
    have hc := (hW h hh m⁻¹ (hN.2.2 m hm)).1
    refine ⟨h⁻¹, uw_inv hh, h * m⁻¹ * h⁻¹, hc, ?_⟩
    rw [Matrix.mul_inv_rev]
    calc m⁻¹ * h⁻¹ = h⁻¹ * h * m⁻¹ * h⁻¹ := by rw [Matrix.nonsing_inv_mul h hd, one_mul]
      _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [mul_assoc]
end Formalism.QuantumDeterminants
