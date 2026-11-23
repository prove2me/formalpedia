-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.orthogonality_of_mackey
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:11.376207+00:00
-- url     : https://prove2.me/submissions/f10f7b74-11ce-4dfc-bc87-d70b21abe265

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey

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
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : OrthOfMackey := by
  unfold OrthOfMackey
  intro K _ _ _ Z _ _ P _ _ ρ U _ ψ hM h hh z hz
  obtain ⟨_, hmul, hex⟩ := hM
  obtain ⟨u0, hu0, hc, hne⟩ := hex h hh
  set S := ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ h z) with hS
  have hz' : ∀ u ∈ U, ρ u z = ((ψ u : 𝓞 K) : K) • z := by
    intro u hu
    unfold eig at hz
    have h1 := (Submodule.mem_iInf _).mp hz ⟨u, hu⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h1
    exact h1
  have hA : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ u0 : 𝓞 K) : K) • S := by
    rw [hS, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨u0, hu0⟩ : U)) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    congr 1
    have key : ψ ((u : P)⁻¹) = ψ u0 * ψ (((u : P) * u0)⁻¹) := by
      rw [← hmul u0 hu0 _ (U.inv_mem (U.mul_mem u.2 hu0))]
      congr 1
      group
    rw [key]
    norm_cast
  have hB : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • S := by
    have e1 : ρ u0 (ρ h z) = ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • ρ h z := by
      have e2 : ρ u0 (ρ h z) = ρ h (ρ (h⁻¹ * u0 * h) z) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [e2, hz' _ hc, map_smul]
    rw [hS, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [e1, map_smul, smul_smul, smul_smul, mul_comm]
  have h3 : (((ψ u0 : 𝓞 K) : K) - ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K)) • S = 0 := by
    rw [sub_smul, ← hA, ← hB, sub_self]
  rcases smul_eq_zero.mp h3 with h0 | h0
  · exact absurd (by exact_mod_cast (sub_eq_zero.mp h0).symm) hne
  · exact h0
end Formalism.EigenvalueLevelCeiling
