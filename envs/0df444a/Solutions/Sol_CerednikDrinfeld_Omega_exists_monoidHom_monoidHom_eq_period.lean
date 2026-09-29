-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_eq_period
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bfc48c15-83fa-57df-b313-47de8612a230

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta
import Theorems.Thm_CerednikDrinfeld_Omega_period_symm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (haz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ a)
    (hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ w) (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u z) :
    ∃ Q : G →* G →* Kˣ, ∀ α β : G, ((Q α β : Kˣ) : K) = period ρ a z₀ α β := by
  have hmem : ∀ (g : PGL(2, K₀)) {x : K}, x ∈ upperHalfPlane K₀ K → pmoebius K₀ g x ∈ upperHalfPlane K₀ K :=
    fun g x hx => pmoebius_mem_upperHalfPlane K₀ hx g
  have hmul : ∀ {x t : K}, x ∈ upperHalfPlane K₀ K → (∀ γ : G, pmoebius K₀ (ρ γ) x ≠ t) →
      ∀ (δ γ : G), pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ δ) x) ≠ t := by
    intro x t hx h δ γ
    rw [← pmoebius_mul K₀ hx, ← map_mul]
    exact h _

  choose c hc using fun α : G =>
    exists_monoidHom_isAutomorphicWithMultiplier_theta ρ ha (hmem (ρ α) ha) hz₀ hz₀a (hmul ha hz₀a α)
      (fun z hz => hΘ _ ha _ (hmem (ρ α) ha) _ hz₀ _ hz)
  have hc' : ∀ α β : G, ((c α β : Kˣ) : K) = period ρ a z₀ α β := fun α β => (hc α).1 β

  have hsymm : ∀ α β : G, period ρ a z₀ α β = period ρ a z₀ β α := fun α β =>
    period_symm ρ ha hz₀ hw hz₀a haz₀ hwa hwz₀ hΘ α β
  refine ⟨MonoidHom.mk' c (fun α₁ α₂ => ?_), fun α β => ?_⟩
  · ext β
    calc ((c (α₁ * α₂) β : Kˣ) : K) = period ρ a z₀ (α₁ * α₂) β := hc' _ _
      _ = period ρ a z₀ β (α₁ * α₂) := hsymm _ _
      _ = ((c β (α₁ * α₂) : Kˣ) : K) := (hc' _ _).symm
      _ = ((c β α₁ : Kˣ) : K) * ((c β α₂ : Kˣ) : K) := by rw [map_mul, Units.val_mul]
      _ = period ρ a z₀ α₁ β * period ρ a z₀ α₂ β := by rw [hc', hc', hsymm β α₁, hsymm β α₂]
      _ = (((c α₁ * c α₂) β : Kˣ) : K) := by rw [MonoidHom.mul_apply, Units.val_mul, hc', hc']
  · rw [MonoidHom.mk'_apply, hc']

end S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period (solution)
