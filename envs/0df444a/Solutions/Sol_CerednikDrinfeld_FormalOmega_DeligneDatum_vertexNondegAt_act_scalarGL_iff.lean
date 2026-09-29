-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.vertexNondegAt_act_scalarGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f943331f-d98a-59c1-8bc1-b9714d5b2da9

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_vertexNondegAt_act_scalarGL_iff

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped Matrix

namespace B24VH

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem map_sup_smul_top {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module B V] [Module B W]
    (Φ : V ≃ₗ[B] W) (S : Submodule B V) (𝔭 : Ideal B) :
    (S ⊔ 𝔭 • ⊤).map Φ.toLinearMap = S.map Φ.toLinearMap ⊔ 𝔭 • ⊤ := by
  rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem act_act (g h : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) :
    FullLattice.act g (FullLattice.act h M) = FullLattice.act (g * h) M :=
  Subtype.ext (latticeMap_mul g h M.1).symm

theorem act_one (M : FullLattice 𝒪 K) : FullLattice.act (1 : Matrix.GeneralLinearGroup (Fin 2) K) M = M :=
  Subtype.ext (latticeMap_one M.1)

theorem vertexNondegAt_of_act (π : 𝒪) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ) (M : FullLattice 𝒪 K)
    (H : d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) M)) : d.VertexNondegAt π 𝔭 M := by
  intro v hv hmem
  have hcv : (c : K) • (v : Fin 2 → K) ∈ (FullLattice.act (scalarGL c) M).1 :=
    mem_latticeMap_scalarGL.mpr ⟨v, v.2, rfl⟩
  apply H ⟨(c : K) • (v : Fin 2 → K), hcv⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨w, hw, hww'⟩ := mem_latticeMap_scalarGL.mp w'.2
    apply hv
    refine ⟨⟨w, hw⟩, ?_⟩
    have h1 : (c : K) • (v : Fin 2 → K) = (c : K) • (algebraMap 𝒪 K π • w) := by
      rw [smul_comm, hww']; exact hw'
    exact smul_right_injective _ c.ne_zero h1
  · rw [d.homothety c M, ← map_sup_smul_top]
    have key : actBaseChange B (scalarGL c) M ((1 : B) ⊗ₜ[𝒪] v) =
        (1 : B) ⊗ₜ[𝒪] (⟨(c : K) • (v : Fin 2 → K), hcv⟩ : ↥(FullLattice.act (scalarGL c) M).1) := by
      show (1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) M.1 v = _
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
    rw [← key]
    exact Submodule.mem_map_of_mem hmem

end B24VH

open B24VH in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ) (M : FullLattice 𝒪 K) :
    d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) M) ↔ d.VertexNondegAt π 𝔭 M := by
  constructor
  · exact vertexNondegAt_of_act π d 𝔭 c M
  · intro h
    have := vertexNondegAt_of_act π d 𝔭 c⁻¹ (FullLattice.act (scalarGL c) M)
    rw [act_act, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, act_one] at this
    exact this h

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_vertexNondegAt_act_scalarGL_iff
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_vertexNondegAt_act_scalarGL_iff (solution)
