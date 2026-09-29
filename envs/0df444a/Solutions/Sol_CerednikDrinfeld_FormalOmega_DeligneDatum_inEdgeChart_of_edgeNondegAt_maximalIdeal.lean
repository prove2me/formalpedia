-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_of_edgeNondegAt_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1287e49b-8409-5ea5-bebc-7579f548aceb

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π (IsLocalRing.maximalIdeal B) M' M) :
    d.InEdgeChart π M' M := by
  intro 𝔭 h𝔭
  have hsub : 𝔭 ≤ IsLocalRing.maximalIdeal B := IsLocalRing.le_maximalIdeal h𝔭.ne_top
  obtain ⟨hle, hπ, h1, h2⟩ := h
  refine ⟨hle, hπ, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
  · have hmono : d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) ≤
        d.line M ⊔ (IsLocalRing.maximalIdeal B • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) :=
      sup_le_sup_left (Submodule.smul_mono_left hsub) _
    exact hmono hmem
  · have hmono : d.line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) ≤
        d.line M' ⊔ (IsLocalRing.maximalIdeal B • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) :=
      sup_le_sup_left (Submodule.smul_mono_left hsub) _
    exact hmono hmem

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal (solution)
