-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.invariantFieldOf_map_conj_eq_map_fracAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/83ab4be6-8a16-528b-bbe5-e357c420f562

import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem I3Conj.mem_invariantFieldOf_map_conj_iff
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M] (g : G) (Γ : Subgroup G) (x : FractionRing M) :
    x ∈ invariantFieldOf K G M (Γ.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ • x ∈ invariantFieldOf K G M Γ := by
  rw [mem_invariantFieldOf_iff, mem_invariantFieldOf_iff]
  constructor
  · intro h δ hδ
    have h1 := h (g * δ * g⁻¹) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)
    rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul] at h1
    exact h1
  · intro h γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
    show (g * δ * g⁻¹) • x = x
    rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul]
    exact h δ hδ

theorem solution
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M] (g : G) (Γ : Subgroup G) :
    invariantFieldOf K G M (Γ.map (MulAut.conj g).toMonoidHom) =
      (invariantFieldOf K G M Γ).map (fracAct G M g).toRingHom := by
  ext x
  rw [I3Conj.mem_invariantFieldOf_map_conj_iff, Subfield.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ • x, h, by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← frac_smul_def, smul_inv_smul]⟩
  · rintro ⟨y, hy, rfl⟩
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← frac_smul_def, inv_smul_smul]
    exact hy

end S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct (solution)
