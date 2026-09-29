-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/125e184e-9c2b-5cb2-b6e1-063e6786e36b

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

theorem solution
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B} (φ : S →+* B)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (h : DS.M →+ D.M) (hh : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ DS D h)
    (LS : DS.M →+ DS.NMod) (hLS : DS.IsCartierLMap LS)
    (K : D.M →+ D.NMod) (hK : D.IsCartierLMap K)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ)
    (hKγ : ∀ i : Fin 2, K (h (γ i)) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS (γ i))) :
    ∀ x : DS.M, K (h x) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS x) := by
  classical

  set N := DS.nMap D h hh.2.2.1 hh.2.2.2.1 with hN

  have hσ : ∀ w : WittVector p S,
      WittVector.map φ (WittVector.frobenius w) = WittVector.frobenius (WittVector.map φ w) :=
    fun w => WittVector.IsPoly.map (WittVector.frobenius_isPoly p) φ w

  have hNsmul : ∀ (w : WittVector p S) (n : DS.NMod), N (w • n) = WittVector.map φ w • N n := by
    intro w n
    obtain ⟨⟨m, m'⟩, rfl⟩ := DS.nMk_surjective n
    rw [smul_nMk, hN, nMap_nMk, nMap_nMk, smul_nMk, hh.1, hh.1, hσ]

  have hV : ∀ y : DS.M, K (h (DS.verschiebung y)) = N (LS (DS.verschiebung y)) := by
    intro y
    rw [hh.2.2.1, hK.map_verschiebung, hLS.map_verschiebung, hN, nMap_nMk, hh.2.2.2.1, map_zero]

  have hT : ∀ (c : S) (i : Fin 2),
      K (h (WittVector.teichmuller p c • γ i)) = N (LS (WittVector.teichmuller p c • γ i)) := by
    intro c i
    rw [hh.1, hK.map_smul, hKγ i, hLS.map_smul, hNsmul, hσ]
  intro x
  obtain ⟨⟨c, y⟩, hx, -⟩ := hγ.2 x
  rw [hx]
  simp only [map_add, map_sum]
  rw [hV y]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact hT (c i) i

end S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq (solution)
