-- Prove2me | solution 1 for CerednikDrinfeld.Omega.period_pmoebius_pmoebius_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4dbdf617-5c90-55c4-9a68-6727e9d71cbb

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_mulEquiv

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) (φ : G ≃* G) (n : PGL(2, K₀))
    (hφ : ∀ g : G, ρ (φ g) = n * ρ g * n⁻¹)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (α β : G) :
    period ρ (pmoebius K₀ n a) (pmoebius K₀ n z₀) (φ α) (φ β) = period ρ a z₀ α β := by

  have hact : ∀ (g : G) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (φ g)) (pmoebius K₀ n x) = pmoebius K₀ n (pmoebius K₀ (ρ g) x) := by
    intro g x hx
    rw [hφ, ← pmoebius_mul K₀ hx, mul_assoc, inv_mul_cancel, mul_one, pmoebius_mul K₀ hx]
  have hna : pmoebius K₀ n a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  have hnz : pmoebius K₀ n z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz₀ _
  simp only [period, theta]

  rw [← Equiv.tprod_eq φ.toEquiv]
  congr 1
  funext δ
  simp only [MulEquiv.coe_toEquiv, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, thetaFactor]
  change crossRatio _ _ (pmoebius K₀ (ρ (φ δ)) _) (pmoebius K₀ (ρ (φ δ)) _) = _

  have hαa : pmoebius K₀ (ρ α) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  have hδa : pmoebius K₀ (ρ δ) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  rw [hact α ha, hact β hz₀, hact δ ha, hact δ hαa]
  exact crossRatio_pmoebius n (pmoebius_mem_upperHalfPlane K₀ hz₀ _) hz₀ hδa
    (pmoebius_mem_upperHalfPlane K₀ hαa _)

end S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_mulEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_mulEquiv (solution)
