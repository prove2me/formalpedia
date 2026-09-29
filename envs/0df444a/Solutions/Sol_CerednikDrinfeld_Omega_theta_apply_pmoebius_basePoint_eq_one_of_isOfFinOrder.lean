-- Prove2me | solution 1 for CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2b4dc467-d222-5add-bcf5-73dbfa9a0beb

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Theorems.Thm_CerednikDrinfeld_Omega_theta_smul_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_swap
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (γ : G) (hγ : IsOfFinOrder γ) :
    theta ρ a b z₀ (pmoebius K₀ (ρ γ) z₀) = 1 := by
  have hγz₀ : pmoebius K₀ (ρ γ) z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz₀ _

  have key : theta ρ a b z₀ (pmoebius K₀ (ρ γ) z₀) = theta ρ (pmoebius K₀ (ρ γ) z₀) z₀ b a := by
    unfold theta
    conv_rhs => rw [← Equiv.tprod_eq (Equiv.inv G)]
    congr 1
    funext δ
    simp only [Equiv.inv_apply, thetaFactor]
    rw [crossRatio_swap]

    have hδa : pmoebius K₀ (ρ δ) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
    have hδb : pmoebius K₀ (ρ δ) b ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hb _
    rw [← crossRatio_pmoebius (ρ δ)⁻¹ hδa hδb hγz₀ hz₀, ← pmoebius_mul K₀ ha, ← pmoebius_mul K₀ hb,
      inv_mul_cancel, map_inv, ← pmoebius_mul K₀ hz₀]
    have h1 : ∀ y : K, pmoebius K₀ (1 : PGL(2, K₀)) y = y := fun y => by simp [pmoebius]
    rw [h1, h1]
  rw [key]

  have e : z₀ = pmoebius K₀ (ρ γ⁻¹) (pmoebius K₀ (ρ γ) z₀) := by
    rw [← pmoebius_mul K₀ hz₀, ← map_mul, inv_mul_cancel, map_one]; simp [pmoebius]
  have e2 := congrArg (fun Q => theta ρ (pmoebius K₀ (ρ γ) z₀) Q b a) e
  rw [e2]
  have hone : ∀ y : K, pmoebius K₀ (1 : PGL(2, K₀)) y = y := fun y => by simp [pmoebius]
  refine theta_smul_eq_one_of_isOfFinOrder K₀ K ϖ hex ρ hρ γ⁻¹ hγ.inv hγz₀ hb ha ?_ ?_
  · intro δ h
    apply hz₀b (γ⁻¹ * δ⁻¹)
    rw [← h, ← pmoebius_mul K₀ hγz₀, ← pmoebius_mul K₀ hz₀, ← map_mul, ← map_mul,
      show γ⁻¹ * δ⁻¹ * δ * γ = 1 by group, map_one, hone]
  · intro δ h
    apply hz₀a (γ⁻¹ * δ⁻¹)
    rw [← h, ← pmoebius_mul K₀ hγz₀, ← pmoebius_mul K₀ hz₀, ← map_mul, ← map_mul,
      show γ⁻¹ * δ⁻¹ * δ * γ = 1 by group, map_one, hone]

end S_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder (solution)
