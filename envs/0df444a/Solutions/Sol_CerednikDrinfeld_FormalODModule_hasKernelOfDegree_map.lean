-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1f6a0ac6-0176-51a2-8649-b589be03ece3

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {B B' : Type u} [CommRing B] [IsNoetherianRing B] [CommRing B'] (g : B →+* B') (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    FormalODModule.HasKernelOfDegree (φ.map g) d := by
  obtain ⟨N, hN⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree φ hφ0 hφ
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map_of_X_pow_mem g φ hφ0 hφ N hN

end S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map (solution)
