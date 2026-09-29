-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8983d33b-1d04-5db0-8119-8428dba7613a

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem VE_main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) :
    ∃ d₀ : DeligneDatum (K := K) π V,
      DeligneDatum.IsBaseChange (K := K) (π := π) (IsScalarTower.toAlgHom 𝒪 V L) d₀ d := by
  classical
  let f : V →ₐ[𝒪] L := IsScalarTower.toAlgHom 𝒪 V L

  let N₀ : ∀ M : FullLattice 𝒪 K, Submodule V (latticeBaseChange 𝒪 K V M) := fun M =>
    Submodule.span V {x : latticeBaseChange 𝒪 K V M | LinearMap.rTensor (↥M.1) f.toLinearMap x ∈ d.line M}

  have hmemN₀ : ∀ (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K V M),
      x ∈ N₀ M ↔ LinearMap.rTensor (↥M.1) f.toLinearMap x ∈ d.line M := by
    intro M x
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => rw [map_zero]; exact (d.line M).zero_mem
      | add y z _ _ hy hz => rw [map_add]; exact (d.line M).add_mem hy hz
      | smul a y _ hy =>
        rw [rTensor_smul_left f M a y]
        exact (d.line M).smul_mem (f a) hy
    · intro hx; exact Submodule.subset_span hx

  have hfin : ∀ M : FullLattice 𝒪 K, Module.Finite 𝒪 ↥M.1 := fun M => Module.Finite.iff_fg.mpr M.2.1

  have hsat : ∀ M : FullLattice 𝒪 K,
      Module.Invertible V (latticeBaseChange 𝒪 K V M ⧸ N₀ M) ∧
        Submodule.span L (LinearMap.rTensor (↥M.1) f.toLinearMap '' (N₀ M : Set (latticeBaseChange 𝒪 K V M))) = d.line M := by
    intro M
    haveI := hfin M
    exact Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing V L (↥M.1) (d.line M) (d.invertible M)
  refine ⟨{ line := N₀
            invertible := fun M => (hsat M).1
            mono := ?_
            homothety := ?_
            nondeg := ?_ }, ?_⟩
  ·
    intro M' M h
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap, hmemN₀, rTensor_inclBaseChange f h x]
    exact d.mono h (Submodule.mem_map_of_mem ((hmemN₀ M' x).1 hx))
  ·
    intro c M
    apply le_antisymm
    · intro x hx
      rw [hmemN₀, d.homothety c M] at hx

      rw [Submodule.mem_map]
      refine ⟨(actBaseChange V (scalarGL c) M).symm x, ?_, by simp⟩
      rw [hmemN₀]
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = LinearMap.rTensor (↥M.1) f.toLinearMap ((actBaseChange V (scalarGL c) M).symm x) := by
        apply (actBaseChange L (scalarGL c) M).injective
        rw [← rTensor_actBaseChange f (scalarGL c) M, LinearEquiv.apply_symm_apply]
        exact hyx
      rw [← this]; exact hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [hmemN₀, d.homothety c M]
      refine ⟨LinearMap.rTensor (↥M.1) f.toLinearMap x, (hmemN₀ M x).1 hx, ?_⟩
      exact (rTensor_actBaseChange f (scalarGL c) M x).symm
  ·
    intro 𝔭 h𝔭
    exact CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing π hπ V hV L d 𝔭 h𝔭
  ·
    intro M
    show d.line M = lineBaseChange f M (N₀ M)
    exact ((hsat M).2).symm

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) :
    ∃ d₀ : DeligneDatum (K := K) π V,
      DeligneDatum.IsBaseChange (K := K) (π := π) (IsScalarTower.toAlgHom 𝒪 V L) d₀ d :=
  VE_main π hπ V hV L d

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero (solution)
