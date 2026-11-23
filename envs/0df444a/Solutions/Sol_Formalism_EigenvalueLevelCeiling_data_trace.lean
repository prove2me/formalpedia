-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.data_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:59.056596+00:00
-- url     : https://prove2.me/submissions/55bd53cd-d4a2-4746-b526-5bbf435d2a85

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : DataTrace := by
  intro K _ _ _ Z _ _ _ _ U _ _ ρ ψ X _ _ _ hfree Θ hΘ z hz heig
  classical
  obtain ⟨φ, rfl⟩ := hz

  obtain ⟨φ', hφ'⟩ : ∃ φ' : X → 𝓞 K, φ' = fun x => ∑ u : U, ψ u⁻¹ * φ (u⁻¹ • x) := ⟨_, rfl⟩
  have hinv : ∀ u : U, ψ u⁻¹ * ψ u = 1 := by
    intro u
    rw [← map_mul, inv_mul_cancel, map_one]
  have h1 : ((Fintype.card U : ℕ) : K) • Θ φ = Θ φ' := by
    have e1 : ∀ u : U, Θ φ = (ψ u⁻¹ : 𝓞 K) • Θ (fun x => φ (u⁻¹ • x)) := by
      intro u
      rw [← hΘ, heig u, algebraMap_smul, smul_smul, hinv, one_smul]
    have e2 : φ' = ∑ u : U, (ψ u⁻¹ : 𝓞 K) • (fun x => φ (u⁻¹ • x)) := by
      rw [hφ']
      ext x
      simp [Finset.sum_apply]
    rw [e2, map_sum]
    simp only [map_smul]
    rw [← Finset.sum_congr rfl (fun u _ => e1 u)]
    simp [Nat.cast_smul_eq_nsmul]
  have hequiv : ∀ (u0 : U) (x : X), φ' (u0⁻¹ • x) = ψ u0 * φ' x := by
    intro u0 x
    rw [hφ']
    simp only
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, mul_smul]
    have := hinv u0
    have e : ψ u0 * (ψ u⁻¹ * ψ u0⁻¹ * φ (u⁻¹ • u0⁻¹ • x)) =
        (ψ u0⁻¹ * ψ u0) * (ψ u⁻¹ * φ (u⁻¹ • u0⁻¹ • x)) := by ring
    rw [e, this, one_mul]
  rw [h1]

  let Ω := MulAction.orbitRel.Quotient U X
  have : Fintype Ω := Fintype.ofFinite _
  let rep : Ω → X := Quotient.out
  have hdec : φ' = ∑ ω : Ω, φ' (rep ω) •
      (fun x => ∑ u : U, if x = u⁻¹ • rep ω then ψ u else 0) := by
    ext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    set ω0 : Ω := Quotient.mk'' x with hω0
    have hx : x ∈ MulAction.orbit U (rep ω0) := by
      have : (Quotient.mk'' (rep ω0) : Ω) = Quotient.mk'' x := Quotient.out_eq' ω0
      exact MulAction.orbitRel_apply.mp (Quotient.eq''.mp this.symm)
    obtain ⟨v, hv⟩ := hx
    have hv' : x = (v⁻¹)⁻¹ • rep ω0 := by rw [inv_inv]; exact hv.symm
    rw [Finset.sum_eq_single ω0]
    · rw [Finset.sum_eq_single v⁻¹]
      · rw [if_pos hv']
        conv_lhs => rw [hv']
        rw [hequiv, mul_comm]
      · intro u _ hu
        rw [if_neg]
        intro hxu
        apply hu
        have e : (u * v) • rep ω0 = rep ω0 := by
          have hv2 : v • rep ω0 = x := hv
          rw [mul_smul, hv2, hxu, smul_inv_smul]
        have := hfree _ _ e
        exact eq_inv_of_mul_eq_one_left this
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ω _ hω
      rw [Finset.sum_eq_zero, mul_zero]
      intro u _
      rw [if_neg]
      intro hxu
      apply hω
      have : (Quotient.mk'' x : Ω) = Quotient.mk'' (rep ω) := by
        apply Quotient.eq''.mpr
        apply MulAction.orbitRel_apply.mpr
        exact ⟨u⁻¹, hxu.symm⟩
      rw [hω0, this]
      exact (Quotient.out_eq' ω).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdec, map_sum]
  refine Submodule.sum_mem _ (fun ω _ => ?_)
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨rep ω, rfl⟩)
end Formalism.EigenvalueLevelCeiling
