-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.Hom.eq_of_comp_act_pow_eq_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1dd9aa6b-05ed-534b-bb98-b84a510e74d3

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {q : ℕ} [Fact q.Prime] {B : Type u} [CommRing B] [IsNoetherianRing B]
    {X X' : FormalODModule q B} (k d : ℕ)
    (hk : FormalODModule.HasKernelOfDegree (X.act (((q : ℕ) : Zp2 q) ^ k)) d)
    (ψ ψ' : FormalODModule.Hom X X')
    (h : ψ.toSeries.comp (X.act (((q : ℕ) : Zp2 q) ^ k)) = ψ'.toSeries.comp (X.act (((q : ℕ) : Zp2 q) ^ k))) :
    ψ = ψ' := by
  apply FormalODModule.Hom.ext
  funext i
  exact CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree (X.act (((q : ℕ) : Zp2 q) ^ k))
    (X.isLawHom_act _).1 hk (ψ.toSeries i) (ψ'.toSeries i) (congrFun h i)

end S_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree (solution)
