-- Prove2me | solution 1 for Deep.NTSupply.count_coe_finprod_primeUnit_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1f6ec8b6-838d-5c57-afdf-b17b0ca66736

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deep_NTSupply_count_coe_finprod_primeUnit_zpow

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K]
    (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : (Function.support n).Finite) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
      (((∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ n v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) :
        FractionalIdeal ((𝓞 K)⁰) K) = n w := by
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => primeUnit K v ^ n v).Finite := by
    refine hn.subset fun v hv => ?_
    rw [Function.mem_support]
    intro h
    exact hv (by simp [h])
  have hmap := MonoidHom.map_finprod (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)) hsupp
  simp only [Units.coeHom_apply] at hmap
  rw [hmap]
  simp_rw [Units.val_zpow_eq_zpow_val, primeUnit_val]
  apply FractionalIdeal.count_finprod K w n
  rw [Filter.eventually_cofinite]
  exact hn

end S_Deep_NTSupply_count_coe_finprod_primeUnit_zpow
end P2MW
export P2MW.S_Deep_NTSupply_count_coe_finprod_primeUnit_zpow (solution)
