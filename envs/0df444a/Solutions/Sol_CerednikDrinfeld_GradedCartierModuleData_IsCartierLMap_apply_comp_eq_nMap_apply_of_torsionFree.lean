-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/98d51878-be98-5c9b-a513-a1030648f764

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] {S T : Type} [CommRing S] [CommRing T]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    (g : S →+* T) (hT : ∀ t : T, (p : T) * t = 0 → t = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p S jS) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p T jT) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' g D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (L' : D'.M →+ D'.NMod) (hL' : D'.IsCartierLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  intro x
  obtain ⟨γ', hγ'⟩ := hD'.1
  have hinj := CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree
    p jT hT D' γ' hγ'
  apply hinj
  rw [hL'.lambda_comp, ← hf.2.1 x]
  obtain ⟨⟨m, m'⟩, hm⟩ := D.nMk_surjective (L x)
  rw [← hL.lambda_comp x, ← hm, CerednikDrinfeld.GradedCartierModuleData.nMap_nMk,
    CerednikDrinfeld.GradedCartierModuleData.lambda_nMk, CerednikDrinfeld.GradedCartierModuleData.lambda_nMk,
    map_add, hf.2.2.1, hf.2.2.2.1]

end S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree (solution)
