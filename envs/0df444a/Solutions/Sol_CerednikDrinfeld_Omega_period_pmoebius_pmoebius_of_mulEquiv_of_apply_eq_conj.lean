-- Prove2me | solution 1 for CerednikDrinfeld.Omega.period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/79c29fe0-f85a-5797-8480-5a6ea53b0356

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ρ₁ : G₁ →* PGL(2, K₀)) (ρ₂ : G₂ →* PGL(2, K₀))
    (e : G₁ ≃* G₂) (n : PGL(2, K₀)) (he : ∀ g : G₁, ρ₂ (e g) = n * ρ₁ g * n⁻¹)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (α β : G₁) :
    period ρ₂ (pmoebius K₀ n a) (pmoebius K₀ n z₀) (e α) (e β) = period ρ₁ a z₀ α β := by

  have hact : ∀ (g : G₁) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ₂ (e g)) (pmoebius K₀ n x) = pmoebius K₀ n (pmoebius K₀ (ρ₁ g) x) := by
    intro g x hx
    rw [he, ← pmoebius_mul K₀ hx, mul_assoc, inv_mul_cancel, mul_one, pmoebius_mul K₀ hx]
  have hna : pmoebius K₀ n a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  have hnz : pmoebius K₀ n z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz₀ _
  simp only [period, theta]

  rw [← Equiv.tprod_eq e.toEquiv]
  congr 1
  funext δ
  simp only [MulEquiv.coe_toEquiv, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, thetaFactor]
  change crossRatio _ _ (pmoebius K₀ (ρ₂ (e δ)) _) (pmoebius K₀ (ρ₂ (e δ)) _) = _
  have hαa : pmoebius K₀ (ρ₁ α) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  have hδa : pmoebius K₀ (ρ₁ δ) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  rw [hact α ha, hact β hz₀, hact δ ha, hact δ hαa]
  exact crossRatio_pmoebius n (pmoebius_mem_upperHalfPlane K₀ hz₀ _) hz₀ hδa
    (pmoebius_mem_upperHalfPlane K₀ hαa _)

end S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj (solution)
