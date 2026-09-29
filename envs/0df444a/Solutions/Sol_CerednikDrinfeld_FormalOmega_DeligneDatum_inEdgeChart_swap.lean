-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/277c6229-03cf-58fa-a3cd-24a984b53637

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped Matrix

namespace B24S

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem map_sup_smul_top {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module B V] [Module B W]
    (Φ : V ≃ₗ[B] W) (S : Submodule B V) (𝔭 : Ideal B) :
    (S ⊔ 𝔭 • ⊤).map Φ.toLinearMap = S.map Φ.toLinearMap ⊔ 𝔭 • ⊤ := by
  rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem edgeNondegAt_swap
    {π : 𝒪} (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {d : DeligneDatum (K := K) π B} {M' M : FullLattice 𝒪 K} (𝔭 : Ideal B) (hd : d.EdgeNondegAt π 𝔭 M' M) :
    d.EdgeNondegAt π 𝔭 (FullLattice.act (scalarGL c) M) M' := by
  obtain ⟨hle, hπ, h1, h2⟩ := hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
    rw [← hwv, hc]
    exact hπ ⟨w, hw⟩
  · intro v
    exact mem_latticeMap_scalarGL.mpr ⟨v, hle v.2, by rw [hc]⟩
  · intro v hv
    apply h2 v
    rintro ⟨w, hw⟩
    apply hv
    exact mem_latticeMap_scalarGL.mpr ⟨w, w.2, by rw [hc]; exact hw.symm⟩
  · intro v' hv' hmem
    obtain ⟨u, hu, huv⟩ := mem_latticeMap_scalarGL.mp v'.2
    have hu' : (u : Fin 2 → K) ∉ M'.1 := by
      intro h
      exact hv' ⟨⟨u, h⟩, by rw [← huv, hc]⟩
    apply h1 ⟨u, hu⟩ hu'
    rw [d.homothety c M, ← map_sup_smul_top] at hmem
    have key : actBaseChange B (scalarGL c) M ((1 : B) ⊗ₜ[𝒪] (⟨u, hu⟩ : ↥M.1)) = (1 : B) ⊗ₜ[𝒪] v' := by
      show (1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) M.1 ⟨u, hu⟩ = (1 : B) ⊗ₜ[𝒪] v'
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
      exact huv
    rw [← key, Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at hmem
    exact hmem

end B24S

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {d : DeligneDatum (K := K) π B} {M' M : FullLattice 𝒪 K} (hd : d.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M) M' :=
  fun 𝔭 h𝔭 => B24S.edgeNondegAt_swap c hc 𝔭 (hd 𝔭 h𝔭)

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap (solution)
