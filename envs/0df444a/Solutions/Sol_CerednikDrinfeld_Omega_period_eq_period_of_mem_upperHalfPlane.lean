-- Prove2me | solution 1 for CerednikDrinfeld.Omega.period_eq_period_of_mem_upperHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/209cb10b-8fec-5307-a30c-e3cdee78f998

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace T4A

theorem theta_pmoebius_pmoebius_divisor
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a a' : K}
    (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K) (α : G) (z₀ z : K) :
    theta ρ (pmoebius K₀ (ρ α) a) (pmoebius K₀ (ρ α) a') z₀ z = theta ρ a a' z₀ z := by
  unfold theta
  have hterm : ∀ γ : G, thetaFactor ρ (pmoebius K₀ (ρ α) a) (pmoebius K₀ (ρ α) a') z₀ z γ =
      thetaFactor ρ a a' z₀ z ((Equiv.mulRight α) γ) := by
    intro γ
    unfold thetaFactor
    rw [Equiv.coe_mulRight, map_mul, pmoebius_mul K₀ ha, pmoebius_mul K₀ ha']
  calc ∏' γ : G, thetaFactor ρ (pmoebius K₀ (ρ α) a) (pmoebius K₀ (ρ α) a') z₀ z γ
      = ∏' γ : G, thetaFactor ρ a a' z₀ z ((Equiv.mulRight α) γ) := tprod_congr hterm
    _ = ∏' γ : G, thetaFactor ρ a a' z₀ z γ := Equiv.tprod_eq (Equiv.mulRight α) _

end T4A

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a a' z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K,
      ThetaMultipliable ρ x y z₀ z)
    (α β : G) :
    period ρ a z₀ α β = period ρ a' z₀ α β := by
  have hmem : ∀ (g : PGL(2, K₀)) {x : K}, x ∈ upperHalfPlane K₀ K → pmoebius K₀ g x ∈ upperHalfPlane K₀ K :=
    fun g x hx => pmoebius_mem_upperHalfPlane K₀ hx g

  have horb : ∀ {x : K}, x ∈ upperHalfPlane K₀ K → (∀ γ : G, pmoebius K₀ (ρ γ) x ≠ z₀) →
      ∀ γ δ : G, pmoebius K₀ (ρ γ) x ≠ pmoebius K₀ (ρ δ) z₀ := by
    intro x hx hxz₀ γ δ h
    apply hxz₀ (δ⁻¹ * γ)
    rw [map_mul, pmoebius_mul K₀ hx, h, ← pmoebius_mul K₀ hz₀, ← map_mul, inv_mul_cancel, map_one, pmoebius_one]
  have hz : pmoebius K₀ (ρ β) z₀ ∈ upperHalfPlane K₀ K := hmem _ hz₀
  have hαa : pmoebius K₀ (ρ α) a ∈ upperHalfPlane K₀ K := hmem _ ha
  have hαa' : pmoebius K₀ (ρ α) a' ∈ upperHalfPlane K₀ K := hmem _ ha'

  have g1 : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a) ≠ pmoebius K₀ (ρ β) z₀ := by
    intro γ; rw [← pmoebius_mul K₀ ha, ← map_mul]; exact horb ha hz₀a _ _
  have g2 : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a) ≠ z₀ := by
    intro γ; rw [← pmoebius_mul K₀ ha, ← map_mul]; exact hz₀a _
  have g3 : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ pmoebius K₀ (ρ β) z₀ := fun γ => horb ha' hz₀a' _ _

  have h1 : theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (ρ β) z₀) *
      theta ρ (pmoebius K₀ (ρ α) a) (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (ρ β) z₀) =
      theta ρ a (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (ρ β) z₀) :=
    theta_mul_theta_eq_theta ρ g1 g2 (hΘ _ ha _ hαa _ hz) (hΘ _ hαa _ hαa' _ hz)
  have h2 : theta ρ a a' z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (ρ β) z₀) =
      theta ρ a (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (ρ β) z₀) :=
    theta_mul_theta_eq_theta ρ g3 hz₀a' (hΘ _ ha _ ha' _ hz) (hΘ _ ha' _ hαa' _ hz)

  have h3 : theta ρ (pmoebius K₀ (ρ α) a) (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (ρ β) z₀) =
      theta ρ a a' z₀ (pmoebius K₀ (ρ β) z₀) :=
    T4A.theta_pmoebius_pmoebius_divisor ρ ha ha' α z₀ _

  have hU : theta ρ a a' z₀ (pmoebius K₀ (ρ β) z₀) ≠ 0 :=
    left_ne_zero_of_mul_eq_one
      (theta_pmoebius_basePoint_mul_inv ρ ha ha' hz₀ hz₀a hz₀a' β (hΘ _ ha _ ha' _ hz) (hΘ _ ha _ ha' _ (hmem _ hz₀)))

  show theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (ρ β) z₀) = theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (ρ β) z₀)
  rw [h3] at h1
  exact mul_right_cancel₀ hU (h1.trans (h2.symm.trans (mul_comm _ _)))

end S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane (solution)
