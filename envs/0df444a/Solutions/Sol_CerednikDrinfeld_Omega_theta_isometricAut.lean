-- Prove2me | solution 1 for CerednikDrinfeld.Omega.theta_isometricAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5657dd6f-0d37-54c9-850b-a833d87bd5be

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_theta_isometricAut

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace NAT

theorem continuous_toRingEquiv {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] (s : IsometricAut K₀ K) :
    Continuous s.toRingEquiv := by
  apply continuous_of_continuousAt_zero s.toRingEquiv
  unfold ContinuousAt
  rw [map_zero, (Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
  intro γ _
  refine ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact lt_of_eq_of_lt (s.vRestrict_map x) hx

end NAT

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (s : IsometricAut K₀ K) {a b z₀ z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) :
    theta ρ (s.toRingEquiv a) (s.toRingEquiv b) (s.toRingEquiv z₀) (s.toRingEquiv z) =
      s.toRingEquiv (theta ρ a b z₀ z) := by
  have hcont : Continuous s.toRingEquiv := NAT.continuous_toRingEquiv s
  have hcont' : Continuous s.toRingEquiv.symm := by
    have h := NAT.continuous_toRingEquiv s⁻¹
    rwa [IsometricAut.inv_toRingEquiv] at h
  unfold theta
  rw [Function.LeftInverse.map_tprod (thetaFactor ρ a b z₀ z) hcont hcont' s.toRingEquiv.symm_apply_apply]
  refine tprod_congr fun γ => ?_
  unfold thetaFactor crossRatio
  rw [map_div₀, map_mul, map_mul, map_sub, map_sub, map_sub, map_sub, s.comm_pmoebius _ ha, s.comm_pmoebius _ hb]

end S_CerednikDrinfeld_Omega_theta_isometricAut
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_theta_isometricAut (solution)
