-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4743ca85-abe3-5afe-b024-9c7f85e6015f

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d)
    (f g : MvPowerSeries (Fin 2) B) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g :=
  CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_residueFields φ hφ0 hφ.1
    (fun κ _ g' _ hfin => CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_field (φ.map g')
      (fun i => by simp [Series.map, hφ0]) hfin) f g h

end S_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree (solution)
