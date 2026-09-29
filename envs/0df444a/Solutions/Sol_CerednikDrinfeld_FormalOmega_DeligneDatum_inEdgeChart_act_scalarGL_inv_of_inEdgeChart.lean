-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_inv_of_inEdgeChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/766a91da-2737-5a3e-8d4b-c5c25c3ff54e

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_inv_of_inEdgeChart

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (hd : d.InEdgeChart π M' M) :
    d.InEdgeChart π M (FullLattice.act (scalarGL c⁻¹) M') := by
  have h1 : d.InEdgeChart π (FullLattice.act (scalarGL c) M) M' :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_swap c hc hd
  have h2 : d.InEdgeChart π (FullLattice.act (scalarGL c⁻¹) (FullLattice.act (scalarGL c) M))
      (FullLattice.act (scalarGL c⁻¹) M') :=
    (CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_iff d
      (FullLattice.act (scalarGL c) M) M' c⁻¹).mpr h1
  have hM : FullLattice.act (scalarGL c⁻¹) (FullLattice.act (scalarGL c) M) = M := by
    apply Subtype.ext
    show latticeMap (scalarGL c⁻¹) (latticeMap (scalarGL c) M.1) = M.1
    rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
  rw [hM] at h2
  exact h2

#print axioms solution

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_inv_of_inEdgeChart
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_inv_of_inEdgeChart (solution)
