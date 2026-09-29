-- Prove2me | solution 1 for CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/12335f7b-6c96-5529-94c6-8a34df0d098b

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M) :
    ∃ H : Subgroup (ZMod M)ˣ, Γ = CohCarrier.GammaH M H := by
  classical

  refine ⟨(Γ.subgroupOf (CongruenceSubgroup.Gamma0 M)).map (CohCarrier.gamma0Units M), ?_⟩

  have hker : ∀ δ : ↥(CongruenceSubgroup.Gamma0 M), CohCarrier.gamma0Units M δ = 1 → (δ : SL(2, ℤ)) ∈ Γ := by
    intro δ hδ
    apply hΓ₁
    rw [CongruenceSubgroup.Gamma1_mem]
    have hd : (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1 := by
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hδ
      simp [CohCarrier.val_gamma0Units] at this
      exact this
    have hc : (((δ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := (CongruenceSubgroup.Gamma0_mem).mp δ.2
    have ha : (((δ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = 1 := by
      have h := CohCarrier.Gamma0_d_mul_a M δ

      have h' : (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) * (((δ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = 1 := by simpa using h
      rwa [hd, one_mul] at h'
    exact ⟨ha, hd, hc⟩
  apply le_antisymm
  · intro γ hγ
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hΓ₀ hγ, ?_⟩
    exact Subgroup.mem_map.mpr ⟨⟨γ, hΓ₀ hγ⟩, Subgroup.mem_subgroupOf.mpr hγ, rfl⟩
  · intro γ hγ
    obtain ⟨hγ0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    obtain ⟨δ, hδΓ, hδ⟩ := Subgroup.mem_map.mp hH
    have hδΓ' : (δ : SL(2, ℤ)) ∈ Γ := Subgroup.mem_subgroupOf.mp hδΓ

    have hk : ((δ⁻¹ * ⟨γ, hγ0⟩ : ↥(CongruenceSubgroup.Gamma0 M)) : SL(2, ℤ)) ∈ Γ := by
      apply hker
      rw [map_mul, map_inv, hδ, inv_mul_cancel]
    have : γ = (δ : SL(2, ℤ)) * ((δ⁻¹ * ⟨γ, hγ0⟩ : ↥(CongruenceSubgroup.Gamma0 M)) : SL(2, ℤ)) := by
      simp
    rw [this]
    exact Γ.mul_mem hδΓ' hk

end S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
end P2MW
export P2MW.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0 (solution)
