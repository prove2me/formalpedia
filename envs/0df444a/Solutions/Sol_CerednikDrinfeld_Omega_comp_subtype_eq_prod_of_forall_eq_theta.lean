-- Prove2me | solution 1 for CerednikDrinfeld.Omega.comp_subtype_eq_prod_of_forall_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2c7c1017-a5f0-58bd-bf64-ca825d9a1097

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer
import Theorems.Thm_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_comp_subtype_eq_prod_of_forall_eq_theta

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

open CerednikDrinfeld in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (c : G →* Kˣ) (hc : ∀ β : G, ((c β : Kˣ) : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (c' : G ⧸ Γ' → (↥Γ' →* Kˣ))
    (hc' : ∀ (q : G ⧸ Γ') (β : ↥Γ'), ((c' q β : Kˣ) : K) =
      theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ (pmoebius K₀ (ρ β) z₀)) :
    c.comp Γ'.subtype = ∏ q : G ⧸ Γ', c' q := by
  classical
  ext β
  rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, Units.coe_prod, Subgroup.coe_subtype, hc]
  simp_rw [hc']
  exact (Omega.theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod K₀ K ϖ hex ρ hρ Γ' s hs ha hb hz₀ hz₀a hz₀b).1 _
    (pmoebius_mem_upperHalfPlane K₀ hz₀ _)

end S_CerednikDrinfeld_Omega_comp_subtype_eq_prod_of_forall_eq_theta
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_comp_subtype_eq_prod_of_forall_eq_theta (solution)
