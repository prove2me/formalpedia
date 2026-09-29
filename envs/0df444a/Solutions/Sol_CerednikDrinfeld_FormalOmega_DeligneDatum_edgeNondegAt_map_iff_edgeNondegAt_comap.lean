-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/efbcb96e-8799-5791-9bc9-2efd74d50cd0

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace EdgeBCSol

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem rTensor_mem_lineBaseChange_sup (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (𝔮 : Ideal B') (x : latticeBaseChange 𝒪 K B L)
    (hx : x ∈ N ⊔ (Ideal.comap f 𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) :
    LinearMap.rTensor (↥L.1) f.toLinearMap x ∈
      lineBaseChange f L N ⊔ (𝔮 • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L)) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine Submodule.add_mem_sup (Submodule.subset_span ⟨y, hy, rfl⟩) ?_
  refine Submodule.smul_induction_on
    (p := fun z => LinearMap.rTensor (↥L.1) f.toLinearMap z ∈ (𝔮 • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L)))
    hz (fun r hr n _ => ?_) (fun a b ha hb => ?_)
  · show LinearMap.rTensor (↥L.1) f.toLinearMap (r • n) ∈ _
    rw [rTensor_smul_left f L r n]
    exact Submodule.smul_mem_smul (Ideal.mem_comap.mp hr) Submodule.mem_top
  · show LinearMap.rTensor (↥L.1) f.toLinearMap (a + b) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ ha hb

theorem one_tmul_not_mem_map_iff (π : 𝒪) (d : DeligneDatum (K := K) π B) (𝔮 : Ideal B') [𝔮.IsPrime]
    (L : FullLattice 𝒪 K) (v : ↥L.1) :
    (1 : B') ⊗ₜ[𝒪] v ∉ (d.map π f).line L ⊔ (𝔮 • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L)) ↔
      (1 : B) ⊗ₜ[𝒪] v ∉ d.line L ⊔ (Ideal.comap f 𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
  constructor
  · intro h hmem
    apply h
    rw [← rTensor_one_tmul f L v]
    exact rTensor_mem_lineBaseChange_sup f L (d.line L) 𝔮 _ hmem
  · intro h
    rw [← rTensor_one_tmul f L v]
    exact rTensor_not_mem_lineBaseChange_sup f L (d.line L) (d.invertible L) 𝔮 _ h

end EdgeBCSol

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (𝔮 : Ideal B') [𝔮.IsPrime] (M' M : FullLattice 𝒪 K) :
    (d.map π f).EdgeNondegAt π 𝔮 M' M ↔ d.EdgeNondegAt π (𝔮.comap f) M' M := by
  unfold DeligneDatum.EdgeNondegAt
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun v hv => (EdgeBCSol.one_tmul_not_mem_map_iff f π d 𝔮 M v).mp (h3 v hv),
      fun v' hv' => (EdgeBCSol.one_tmul_not_mem_map_iff f π d 𝔮 M' v').mp (h4 v' hv')⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun v hv => (EdgeBCSol.one_tmul_not_mem_map_iff f π d 𝔮 M v).mpr (h3 v hv),
      fun v' hv' => (EdgeBCSol.one_tmul_not_mem_map_iff f π d 𝔮 M' v').mpr (h4 v' hv')⟩

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap (solution)
