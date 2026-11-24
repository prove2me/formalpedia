-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.orbitsInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:39.769153+00:00
-- url     : https://prove2.me/submissions/b628472b-e689-47b5-a48e-84ee0d77b7a6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_BehrendSets_TranslateMean
import Definitions.Def_Formalism_BehrendSets_FinalE
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
theorem _root_.solution : OrbitsInt := by
  intro e φ hφ
  have hp : ∀ g : GG e, (placeOf g).2 = g.2 ∧ (placeOf g).1 = (g.1.1 * g.1.2, 1) := by
    intro g
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨by simp [placeOf, hg], ?_⟩
      ext <;> simp [placeOf, hg]
    · refine ⟨by simp [placeOf, hg, cc], ?_⟩
      ext <;> simp [placeOf, hg, cc, c0]
  have hsq : ∀ x : ℤˣ, ∀ i : ℤ, x ^ i = if Even i then 1 else x := by
    intro x i
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · simp [zpow_mul, Int.units_sq]
    · have : ¬ Even (2 * k + 1) := by simp
      simp [zpow_add, zpow_mul, Int.units_sq]
  refine ⟨⟨?_, rfl, ?_, orderOf_inv φ⟩, ?_⟩
  · rcases hφ with h | h <;> rw [Prod.fst_inv, h] <;> ext <;> simp [c0]
  · rw [Prod.snd_inv, orderOf_inv]
  · intro τ i
    have h2 : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_Psi_iff, mem_Psi_iff]
      have : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [this, h2, hsq]
      rcases Int.units_eq_one_or τ.1.2 with ht | ht <;> by_cases hi : Even i <;> simp [ht, hi]
    · rw [(hp _).1]; simp
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, c0]
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, sg]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
