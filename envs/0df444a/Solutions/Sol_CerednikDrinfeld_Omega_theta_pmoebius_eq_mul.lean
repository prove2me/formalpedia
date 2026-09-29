-- Prove2me | solution 1 for CerednikDrinfeld.Omega.theta_pmoebius_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a44236d3-64e3-5276-ac28-0f3e93273603

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β : G)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ₀ : ThetaMultipliable ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z) =
      theta ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀ * theta ρ a b z₀ z := by

  have hfac : ∀ γ : G, thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z) γ =
      thetaFactor ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀ (β⁻¹ * γ) * thetaFactor ρ a b z₀ z (β⁻¹ * γ) := by
    intro γ
    have hβz : pmoebius K₀ (ρ β) z ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz (ρ β)
    have hγa : pmoebius K₀ (ρ γ) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha (ρ γ)
    have hγb : pmoebius K₀ (ρ γ) b ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hb (ρ γ)
    have hinv := CerednikDrinfeld.Omega.crossRatio_pmoebius (ρ β⁻¹) hβz hz₀ hγa hγb
    rw [thetaFactor, ← hinv, ← pmoebius_mul K₀ hz, ← pmoebius_mul K₀ ha, ← pmoebius_mul K₀ hb]
    simp only [← map_mul, inv_mul_cancel, map_one, pmoebius_one]
    rw [thetaFactor, thetaFactor, mul_comm]
    exact (CerednikDrinfeld.Omega.crossRatio_mul_crossRatio z z₀ (pmoebius K₀ (ρ β⁻¹) z₀)
      (pmoebius K₀ (ρ (β⁻¹ * γ)) a) (pmoebius K₀ (ρ (β⁻¹ * γ)) b) (hz₀a _).symm (hz₀b _).symm).symm

  have hre : thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z) =
      fun γ : G => (fun δ : G => thetaFactor ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀ δ * thetaFactor ρ a b z₀ z δ)
        (Equiv.mulLeft β⁻¹ γ) := by
    funext γ
    rw [Equiv.coe_mulLeft]
    exact hfac γ
  rw [theta, theta, theta, hre, Equiv.tprod_eq]
  exact Multipliable.tprod_mul hΘ₀ hΘ

end S_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul (solution)
