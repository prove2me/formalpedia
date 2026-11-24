-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.liftForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:26.810975+00:00
-- url     : https://prove2.me/submissions/1c8423f9-7a6b-4f73-b2f4-eb7892195d96

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution {G : Type} [Group G] (Γ U : Subgroup G)
    (hst : ∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1)
    {W V : Type} [MulAction U W] [MulAction U V] (p : W → V)
    (hp : ∀ (u : U) (x : W), p (u • x) = u • p x) (f : G → V) (hf : IsForm Γ U f)
    (hs : ∀ g, ∃ x, p x = f g) : ∃ f' : G → W, IsForm Γ U f' ∧ ∀ g, p (f' g) = f g := by
  classical
  let S : G → Set G := fun g => {g' | ∃ γ ∈ Γ, ∃ u : U, g' = γ * g * (u : G)}
  have hSself : ∀ g, g ∈ S g := fun g => ⟨1, Γ.one_mem, 1, by simp⟩
  have hSeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, S (γ * g * (u : G)) = S g := by
    intro g γ hγ u
    ext g'
    constructor
    · rintro ⟨γ', hγ', u', rfl⟩
      exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, u * u', by simp [mul_assoc]⟩
    · rintro ⟨γ', hγ', u', rfl⟩
      exact ⟨γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), u⁻¹ * u', by simp [mul_assoc]⟩
  haveI : Nonempty G := ⟨1⟩
  let rep : G → G := fun g => Classical.epsilon (fun g' => g' ∈ S g)
  have hrep : ∀ g, rep g ∈ S g := fun g => Classical.epsilon_spec (p := fun g' => g' ∈ S g) ⟨g, hSself g⟩
  have hrepeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, rep (γ * g * (u : G)) = rep g := by
    intro g γ hγ u
    show Classical.epsilon (fun g' => g' ∈ S (γ * g * (u : G))) = Classical.epsilon (fun g' => g' ∈ S g)
    rw [hSeq g γ hγ u]
  have hdec : ∀ g, ∃ γ : G, ∃ u : U, γ ∈ Γ ∧ g = γ * rep g * (u : G) := by
    intro g
    obtain ⟨γ, hγ, u, h⟩ := hrep g
    exact ⟨γ⁻¹, u⁻¹, Γ.inv_mem hγ, by rw [h]; simp [mul_assoc]⟩
  choose γf uf hγf hg using hdec
  choose x hx using hs
  refine ⟨fun g => (uf g)⁻¹ • x (rep g), ?_, ?_⟩
  · intro γ hγ u g
    have hr := hrepeq g γ hγ u
    have e1 := hg (γ * g * (u : G))
    rw [hr] at e1
    have e0 := hg g
    set r := rep g
    set γ1 := γf (γ * g * (u : G))
    set u1 := uf (γ * g * (u : G))
    set γ0 := γf g
    set u0 := uf g
    have e2 : γ * (γ0 * r * (u0 : G)) * (u : G) = γ1 * r * (u1 : G) := by rw [← e0]; exact e1
    have e3 : r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = (u1 : G) * ((u0 : G) * (u : G))⁻¹ := by
      have : γ * γ0 * r = γ1 * r * (u1 : G) * ((u0 : G) * (u : G))⁻¹ := by
        rw [← e2]; simp [mul_assoc]
      calc r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = r⁻¹ * γ1⁻¹ * (γ * γ0 * r) := by simp [mul_assoc]
        _ = _ := by rw [this]; simp [mul_assoc]
    have e4 : γ1⁻¹ * (γ * γ0) = 1 := by
      apply hst r _ (Γ.mul_mem (Γ.inv_mem (hγf _)) (Γ.mul_mem hγ (hγf _)))
      rw [e3]
      exact U.mul_mem u1.2 (U.inv_mem (U.mul_mem u0.2 u.2))
    have e5 : (u1 : G) = (u0 : G) * (u : G) := by
      rw [e4] at e3
      simp only [mul_one, inv_mul_cancel] at e3
      exact (mul_inv_eq_one.1 e3.symm)
    have e6 : u1 = u0 * u := Subtype.ext e5
    show u1⁻¹ • x (rep (γ * g * (u : G))) = u⁻¹ • u0⁻¹ • x r
    rw [hr, e6, mul_inv_rev, mul_smul]
  · intro g
    show p ((uf g)⁻¹ • x (rep g)) = f g
    rw [hp, hx]
    conv_rhs => rw [hg g]
    exact (hf _ (hγf g) _ _).symm
end Formalism.HermitianLattices.StabilizerLevels.PfB
