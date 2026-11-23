-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.gmap_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:27.496295+00:00
-- url     : https://prove2.me/submissions/be4bcf8c-8661-4067-951f-95b0435cadb0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution (g : K ≃ₗ[K] K) (I M : Submodule (𝓞 K) K) : I * gmap g M = gmap g (I * M) := by
  have key : ∀ x y : K, g (x * y) = x * g y := fun x y => by
    simpa only [smul_eq_mul] using g.map_smul x y
  unfold gmap
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * m, Submodule.mul_mem_mul hi hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun i hi m hm => ?_)
    rw [Submodule.mem_comap]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map_of_mem hm)
end Formalism.HermitianLattices.Ext.L3.RankOne
