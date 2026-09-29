-- Prove2me | solution 1 for CerednikDrinfeld.Omega.theta_mul_theta_basePoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/32bbe3b9-e846-5a90-bf3f-9a7734d36f66

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_theta_mul_theta_basePoint

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z w : K}
    (hza : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hzb : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z)
    (h₀ : ThetaMultipliable ρ a b z₀ z) (h₁ : ThetaMultipliable ρ a b z w) :
    theta ρ a b z₀ z * theta ρ a b z w = theta ρ a b z₀ w := by
  simp only [theta]
  rw [← Multipliable.tprod_mul h₀ h₁]
  congr 1
  funext γ
  simp only [thetaFactor]
  rw [mul_comm]
  exact crossRatio_mul_crossRatio w z z₀ _ _ (Ne.symm (hza γ)) (Ne.symm (hzb γ))

end S_CerednikDrinfeld_Omega_theta_mul_theta_basePoint
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_theta_mul_theta_basePoint (solution)
