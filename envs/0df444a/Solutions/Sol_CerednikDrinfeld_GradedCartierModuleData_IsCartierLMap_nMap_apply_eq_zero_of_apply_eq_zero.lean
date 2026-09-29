-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.nMap_apply_eq_zero_of_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b42f6d4f-3f88-5ce9-8dfe-68bfe7c8aa6e

import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero

set_option autoImplicit false

namespace C6bCore

p2m_open "CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData"

theorem map_frobenius_comm (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (φ : S →+* B) (w : WittVector p S) :
    WittVector.map φ (WittVector.frobenius w) = WittVector.frobenius (WittVector.map φ w) :=
  WittVector.IsPoly.map (WittVector.frobenius_isPoly p) φ w

theorem nMap_smul (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : Zp2 p →+* S} (φ : S →+* B)
    (Dl : GradedCartierModuleData p S jS) (D : GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : IsBaseChangeAlong φ Dl D f) (w : WittVector p S) (z : Dl.NMod) :
    Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (w • z) =
      WittVector.map φ w • Dl.nMap D f hf.2.2.1 hf.2.2.2.1 z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := Dl.nMk_surjective z
  rw [smul_nMk, nMap_nMk, nMap_nMk, smul_nMk, hf.1, hf.1, map_frobenius_comm]

end C6bCore

theorem solution
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (hLl : Dl.IsCartierLMap Ll)
    (x : Dl.M) (hx : f x = 0) :
    Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x) = 0 := by
  obtain ⟨γ, hγ, hγ'⟩ := hf.2.2.2.2.2
  obtain ⟨c, y, hc, hy, hx'⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
      p jS φ Dl D f hf γ hγ hγ' x hx

  have hterm : ∀ i : Fin 2,
      Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll (WittVector.teichmuller p (c i) • γ i)) = 0 := by
    intro i
    rw [hLl.map_smul, C6bCore.nMap_smul p φ Dl D f hf, C6bCore.map_frobenius_comm,
      WittVector.map_teichmuller, hc i, WittVector.teichmuller_zero, map_zero, zero_smul]
  rw [hx', map_add, map_add, map_sum, map_sum, Finset.sum_eq_zero (fun i _ => hterm i), zero_add,
    hLl.map_verschiebung, CerednikDrinfeld.GradedCartierModuleData.nMap_nMk, hf.2.2.2.1, hy,
    map_zero, map_zero, Prod.mk_zero_zero, map_zero]

end S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero (solution)
